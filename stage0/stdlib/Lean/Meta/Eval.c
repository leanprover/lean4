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
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
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
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
lean_object* v_name_46_; lean_object* v_defValue_47_; lean_object* v_map_48_; lean_object* v___x_49_; 
v_name_46_ = lean_ctor_get(v_opt_45_, 0);
v_defValue_47_ = lean_ctor_get(v_opt_45_, 1);
v_map_48_ = lean_ctor_get(v_opts_44_, 0);
v___x_49_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_48_, v_name_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_inc(v_defValue_47_);
return v_defValue_47_;
}
else
{
lean_object* v_val_50_; 
v_val_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_50_);
lean_dec_ref_known(v___x_49_, 1);
if (lean_obj_tag(v_val_50_) == 3)
{
lean_object* v_v_51_; 
v_v_51_ = lean_ctor_get(v_val_50_, 0);
lean_inc(v_v_51_);
lean_dec_ref_known(v_val_50_, 1);
return v_v_51_;
}
else
{
lean_dec(v_val_50_);
lean_inc(v_defValue_47_);
return v_defValue_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_52_, lean_object* v_opt_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v_opts_52_, v_opt_53_);
lean_dec_ref(v_opt_53_);
lean_dec_ref(v_opts_52_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v___x_55_, lean_object* v___x_56_, lean_object* v_as_57_, size_t v_i_58_, size_t v_stop_59_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = lean_usize_dec_eq(v_i_58_, v_stop_59_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_uget_borrowed(v_as_57_, v_i_58_);
v___x_66_ = l_Lean_Environment_isImportedConst(v___x_55_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_lt(v___x_67_, v___x_56_);
if (v___x_68_ == 0)
{
goto v___jp_60_;
}
else
{
return v___x_68_;
}
}
else
{
goto v___jp_60_;
}
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
v___jp_60_:
{
size_t v___x_61_; size_t v___x_62_; 
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_add(v_i_58_, v___x_61_);
v_i_58_ = v___x_62_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_as_72_, lean_object* v_i_73_, lean_object* v_stop_74_){
_start:
{
size_t v_i_boxed_75_; size_t v_stop_boxed_76_; uint8_t v_res_77_; lean_object* v_r_78_; 
v_i_boxed_75_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_stop_boxed_76_ = lean_unbox_usize(v_stop_74_);
lean_dec(v_stop_74_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v___x_70_, v___x_71_, v_as_72_, v_i_boxed_75_, v_stop_boxed_76_);
lean_dec_ref(v_as_72_);
lean_dec(v___x_71_);
lean_dec_ref(v___x_70_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = l_Lean_Elab_abortCommandExceptionId;
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___boxed(lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object* v_msgData_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_89_);
v_toCold_96_ = lean_ctor_get(v___y_90_, 0);
v_mctx_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_95_);
v_lctx_98_ = lean_ctor_get(v___y_88_, 2);
v_options_99_ = lean_ctor_get(v_toCold_96_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_94_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_87_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v___x_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 2);
v___x_117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_ref_116_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_ref_116_);
lean_ctor_set(v___x_122_, 1, v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set_tag(v___x_120_, 1);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_msg_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v_x_134_, 1);
v___x_141_ = l_Lean_stringToMessageData(v_a_140_);
v___x_142_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_141_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
return v___x_142_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v_x_134_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v_x_134_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v_x_134_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 0);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg___boxed(lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(lean_object* v_constName_158_, uint8_t v_checkMeta_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v_env_166_; uint8_t v___x_167_; 
v___x_165_ = lean_st_ref_get(v___y_163_);
v_env_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_env_166_);
lean_dec(v___x_165_);
lean_inc(v_constName_158_);
v___x_167_ = lean_has_compile_error(v_env_166_, v_constName_158_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v_env_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_168_ = lean_st_ref_get(v___y_163_);
v_env_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_env_169_);
lean_dec(v___x_168_);
v___x_170_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_162_);
v___x_171_ = l_Lean_Environment_evalConst___redArg(v_env_169_, v___x_170_, v_constName_158_, v_checkMeta_159_);
lean_dec(v_constName_158_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v_env_169_);
v___x_172_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_171_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; lean_object* v_env_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref_known(v___x_173_, 1);
v___x_174_ = lean_st_ref_get(v___y_163_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_162_);
v___x_177_ = l_Lean_Environment_evalConst___redArg(v_env_175_, v___x_176_, v_constName_158_, v_checkMeta_159_);
lean_dec(v_constName_158_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_env_175_);
v___x_178_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_177_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_178_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_constName_158_);
v_a_179_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_173_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_173_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg___boxed(lean_object* v_constName_187_, lean_object* v_checkMeta_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v_checkMeta_boxed_194_; lean_object* v_res_195_; 
v_checkMeta_boxed_194_ = lean_unbox(v_checkMeta_188_);
v_res_195_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_187_, v_checkMeta_boxed_194_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_o_199_, lean_object* v_k_200_, uint8_t v_v_201_){
_start:
{
lean_object* v_map_202_; uint8_t v_hasTrace_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_217_; 
v_map_202_ = lean_ctor_get(v_o_199_, 0);
v_hasTrace_203_ = lean_ctor_get_uint8(v_o_199_, sizeof(void*)*1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_o_199_);
if (v_isSharedCheck_217_ == 0)
{
v___x_205_ = v_o_199_;
v_isShared_206_ = v_isSharedCheck_217_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_map_202_);
lean_dec(v_o_199_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_217_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_207_, 0, v_v_201_);
lean_inc(v_k_200_);
v___x_208_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_200_, v___x_207_, v_map_202_);
if (v_hasTrace_203_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_212_; 
v___x_209_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1));
v___x_210_ = l_Lean_Name_isPrefixOf(v___x_209_, v_k_200_);
lean_dec(v_k_200_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_212_ = v___x_205_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_208_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_210_);
return v___x_212_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v_k_200_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_215_ = v___x_205_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_216_, sizeof(void*)*1, v_hasTrace_203_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_o_218_, lean_object* v_k_219_, lean_object* v_v_220_){
_start:
{
uint8_t v_v_boxed_221_; lean_object* v_res_222_; 
v_v_boxed_221_ = lean_unbox(v_v_220_);
v_res_222_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_o_218_, v_k_219_, v_v_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_opts_223_, lean_object* v_opt_224_, uint8_t v_val_225_){
_start:
{
lean_object* v_name_226_; lean_object* v___x_227_; 
v_name_226_ = lean_ctor_get(v_opt_224_, 0);
lean_inc(v_name_226_);
lean_dec_ref(v_opt_224_);
v___x_227_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_opts_223_, v_name_226_, v_val_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_opts_228_, lean_object* v_opt_229_, lean_object* v_val_230_){
_start:
{
uint8_t v_val_boxed_231_; lean_object* v_res_232_; 
v_val_boxed_231_ = lean_unbox(v_val_230_);
v_res_232_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_opts_228_, v_opt_229_, v_val_boxed_231_);
return v_res_232_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
lean_ctor_set(v___x_239_, 3, v___x_238_);
lean_ctor_set(v___x_239_, 4, v___x_238_);
lean_ctor_set(v___x_239_, 5, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_box(0);
v___x_245_ = lean_unsigned_to_nat(16u);
v___x_246_ = lean_mk_array(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_253_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_ctor_set(v___x_254_, 2, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_258_, lean_object* v_checkType_259_, uint8_t v_safety_260_, lean_object* v_value_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; uint16_t v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_322_; lean_object* v___y_323_; uint8_t v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; uint8_t v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; uint16_t v___y_334_; lean_object* v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; uint8_t v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; uint16_t v___y_368_; uint8_t v___y_369_; uint8_t v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; uint8_t v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; uint8_t v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; uint16_t v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; uint8_t v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; uint8_t v___y_443_; lean_object* v___y_444_; uint8_t v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; uint16_t v___y_451_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint16_t v___y_485_; uint8_t v___y_486_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; uint8_t v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; lean_object* v___y_513_; uint16_t v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_558_; uint16_t v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_589_; lean_object* v___y_590_; uint8_t v___y_591_; uint8_t v___y_592_; uint16_t v___y_593_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; uint8_t v___y_601_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; uint8_t v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_nextMacroScope_755_; lean_object* v_ngen_756_; lean_object* v_auxDeclNGen_757_; lean_object* v_traceState_758_; lean_object* v_recordedDeps_759_; lean_object* v_messages_760_; lean_object* v_infoState_761_; lean_object* v_snapshotTasks_762_; lean_object* v___y_763_; lean_object* v___x_782_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_782_ = lean_st_ref_get(v___y_265_);
lean_inc_ref(v_value_261_);
v___x_796_ = l_Lean_Expr_getUsedConstants(v_value_261_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_array_get_size(v___x_796_);
v___x_799_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v___x_796_);
lean_dec(v___x_782_);
goto v___jp_783_;
}
else
{
if (v___x_799_ == 0)
{
lean_dec_ref(v___x_796_);
lean_dec(v___x_782_);
goto v___jp_783_;
}
else
{
lean_object* v_env_800_; size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v_env_800_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_800_);
lean_dec(v___x_782_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_798_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v_env_800_, v___x_798_, v___x_796_, v___x_801_, v___x_802_);
lean_dec_ref(v___x_796_);
lean_dec_ref(v_env_800_);
if (v___x_803_ == 0)
{
goto v___jp_783_;
}
else
{
goto v___jp_712_;
}
}
}
v___jp_267_:
{
lean_object* v_toCold_279_; lean_object* v_currRecDepth_280_; lean_object* v_ref_281_; uint8_t v_suppressElabErrors_282_; uint8_t v_isRecordingDeps_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_320_; 
v_toCold_279_ = lean_ctor_get(v___y_277_, 0);
v_currRecDepth_280_ = lean_ctor_get(v___y_277_, 1);
v_ref_281_ = lean_ctor_get(v___y_277_, 2);
v_suppressElabErrors_282_ = lean_ctor_get_uint8(v___y_277_, sizeof(void*)*3 + 2);
v_isRecordingDeps_283_ = lean_ctor_get_uint8(v___y_277_, sizeof(void*)*3 + 3);
v_isSharedCheck_320_ = !lean_is_exclusive(v___y_277_);
if (v_isSharedCheck_320_ == 0)
{
v___x_285_ = v___y_277_;
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_ref_281_);
lean_inc(v_currRecDepth_280_);
lean_inc(v_toCold_279_);
lean_dec(v___y_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_fileName_287_; lean_object* v_fileMap_288_; lean_object* v_currNamespace_289_; lean_object* v_openDecls_290_; lean_object* v_initHeartbeats_291_; lean_object* v_maxHeartbeats_292_; lean_object* v_quotContext_293_; lean_object* v_currMacroScope_294_; lean_object* v_cancelTk_x3f_295_; lean_object* v_inheritedTraceOptions_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_317_; 
v_fileName_287_ = lean_ctor_get(v_toCold_279_, 0);
v_fileMap_288_ = lean_ctor_get(v_toCold_279_, 1);
v_currNamespace_289_ = lean_ctor_get(v_toCold_279_, 4);
v_openDecls_290_ = lean_ctor_get(v_toCold_279_, 5);
v_initHeartbeats_291_ = lean_ctor_get(v_toCold_279_, 6);
v_maxHeartbeats_292_ = lean_ctor_get(v_toCold_279_, 7);
v_quotContext_293_ = lean_ctor_get(v_toCold_279_, 8);
v_currMacroScope_294_ = lean_ctor_get(v_toCold_279_, 9);
v_cancelTk_x3f_295_ = lean_ctor_get(v_toCold_279_, 10);
v_inheritedTraceOptions_296_ = lean_ctor_get(v_toCold_279_, 11);
v_isSharedCheck_317_ = !lean_is_exclusive(v_toCold_279_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_318_ = lean_ctor_get(v_toCold_279_, 3);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_toCold_279_, 2);
lean_dec(v_unused_319_);
v___x_298_ = v_toCold_279_;
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_inheritedTraceOptions_296_);
lean_inc(v_cancelTk_x3f_295_);
lean_inc(v_currMacroScope_294_);
lean_inc(v_quotContext_293_);
lean_inc(v_maxHeartbeats_292_);
lean_inc(v_initHeartbeats_291_);
lean_inc(v_openDecls_290_);
lean_inc(v_currNamespace_289_);
lean_inc(v_fileMap_288_);
lean_inc(v_fileName_287_);
lean_dec(v_toCold_279_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_268_, v___y_274_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 3, v___x_300_);
lean_ctor_set(v___x_298_, 2, v___y_268_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fileName_287_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_fileMap_288_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v___y_268_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_currNamespace_289_);
lean_ctor_set(v_reuseFailAlloc_316_, 5, v_openDecls_290_);
lean_ctor_set(v_reuseFailAlloc_316_, 6, v_initHeartbeats_291_);
lean_ctor_set(v_reuseFailAlloc_316_, 7, v_maxHeartbeats_292_);
lean_ctor_set(v_reuseFailAlloc_316_, 8, v_quotContext_293_);
lean_ctor_set(v_reuseFailAlloc_316_, 9, v_currMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_316_, 10, v_cancelTk_x3f_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 11, v_inheritedTraceOptions_296_);
v___x_302_ = v_reuseFailAlloc_316_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_302_);
v___x_304_ = v___x_285_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_currRecDepth_280_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_ref_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*3 + 2, v_suppressElabErrors_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*3 + 3, v_isRecordingDeps_283_);
v___x_304_ = v_reuseFailAlloc_315_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
lean_ctor_set_uint16(v___x_304_, sizeof(void*)*3, v___y_276_);
v___x_305_ = l_Lean_addAndCompile(v___y_270_, v___y_269_, v___y_272_, v___x_304_, v___y_278_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v___x_306_; 
lean_dec_ref_known(v___x_305_, 1);
v___x_306_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v___y_275_, v_checkMeta_258_, v___y_271_, v___y_273_, v___x_304_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___x_304_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_271_);
return v___x_306_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v___x_304_);
lean_dec(v___y_278_);
lean_dec(v___y_275_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_271_);
v_a_307_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_305_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
}
}
v___jp_321_:
{
lean_object* v___x_335_; lean_object* v_env_336_; lean_object* v_nextMacroScope_337_; lean_object* v_ngen_338_; lean_object* v_auxDeclNGen_339_; lean_object* v_traceState_340_; lean_object* v_recordedDeps_341_; lean_object* v_messages_342_; lean_object* v_infoState_343_; lean_object* v_snapshotTasks_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v___x_335_ = lean_st_ref_take(v___y_329_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
v_nextMacroScope_337_ = lean_ctor_get(v___x_335_, 1);
v_ngen_338_ = lean_ctor_get(v___x_335_, 2);
v_auxDeclNGen_339_ = lean_ctor_get(v___x_335_, 3);
v_traceState_340_ = lean_ctor_get(v___x_335_, 4);
v_recordedDeps_341_ = lean_ctor_get(v___x_335_, 6);
v_messages_342_ = lean_ctor_get(v___x_335_, 7);
v_infoState_343_ = lean_ctor_get(v___x_335_, 8);
v_snapshotTasks_344_ = lean_ctor_get(v___x_335_, 9);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_335_, 5);
lean_dec(v_unused_354_);
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snapshotTasks_344_);
lean_inc(v_infoState_343_);
lean_inc(v_messages_342_);
lean_inc(v_recordedDeps_341_);
lean_inc(v_traceState_340_);
lean_inc(v_auxDeclNGen_339_);
lean_inc(v_ngen_338_);
lean_inc(v_nextMacroScope_337_);
lean_inc(v_env_336_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l_Lean_Kernel_enableDiag(v_env_336_, v___y_331_);
lean_inc_ref(v___y_323_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 5, v___y_323_);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_nextMacroScope_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_ngen_338_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_auxDeclNGen_339_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_traceState_340_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v___y_323_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_recordedDeps_341_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v_messages_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v_infoState_343_);
lean_ctor_set(v_reuseFailAlloc_352_, 9, v_snapshotTasks_344_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_st_ref_put(v___y_329_, v___x_350_);
v___y_268_ = v___y_326_;
v___y_269_ = v___y_327_;
v___y_270_ = v___y_322_;
v___y_271_ = v___y_328_;
v___y_272_ = v___y_324_;
v___y_273_ = v___y_330_;
v___y_274_ = v___y_325_;
v___y_275_ = v___y_333_;
v___y_276_ = v___y_334_;
v___y_277_ = v___y_332_;
v___y_278_ = v___y_329_;
goto v___jp_267_;
}
}
}
v___jp_355_:
{
if (v___y_369_ == 0)
{
if (v___y_359_ == 0)
{
v___y_268_ = v___y_361_;
v___y_269_ = v___y_362_;
v___y_270_ = v___y_356_;
v___y_271_ = v___y_363_;
v___y_272_ = v___y_358_;
v___y_273_ = v___y_365_;
v___y_274_ = v___y_360_;
v___y_275_ = v___y_367_;
v___y_276_ = v___y_368_;
v___y_277_ = v___y_366_;
v___y_278_ = v___y_364_;
goto v___jp_267_;
}
else
{
v___y_322_ = v___y_356_;
v___y_323_ = v___y_357_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_360_;
v___y_326_ = v___y_361_;
v___y_327_ = v___y_362_;
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
v___y_330_ = v___y_365_;
v___y_331_ = v___y_369_;
v___y_332_ = v___y_366_;
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
goto v___jp_321_;
}
}
else
{
if (v___y_359_ == 0)
{
v___y_322_ = v___y_356_;
v___y_323_ = v___y_357_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_360_;
v___y_326_ = v___y_361_;
v___y_327_ = v___y_362_;
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
v___y_330_ = v___y_365_;
v___y_331_ = v___y_369_;
v___y_332_ = v___y_366_;
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
goto v___jp_321_;
}
else
{
v___y_268_ = v___y_361_;
v___y_269_ = v___y_362_;
v___y_270_ = v___y_356_;
v___y_271_ = v___y_363_;
v___y_272_ = v___y_358_;
v___y_273_ = v___y_365_;
v___y_274_ = v___y_360_;
v___y_275_ = v___y_367_;
v___y_276_ = v___y_368_;
v___y_277_ = v___y_366_;
v___y_278_ = v___y_364_;
goto v___jp_267_;
}
}
}
v___jp_370_:
{
uint16_t v___x_382_; lean_object* v___x_383_; lean_object* v_env_384_; uint8_t v___x_385_; uint16_t v___x_386_; uint16_t v___x_387_; uint16_t v___x_388_; uint8_t v___x_389_; 
v___x_382_ = l_Lean_OptionFlags_ofOptions(v___y_381_);
v___x_383_ = lean_st_ref_get(v___y_375_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v___x_385_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_384_);
lean_dec_ref(v_env_384_);
v___x_386_ = 512;
v___x_387_ = lean_uint16_land(v___x_382_, v___x_386_);
v___x_388_ = 0;
v___x_389_ = lean_uint16_dec_eq(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
v___y_356_ = v___y_372_;
v___y_357_ = v___y_374_;
v___y_358_ = v___y_376_;
v___y_359_ = v___x_385_;
v___y_360_ = v___y_379_;
v___y_361_ = v___y_381_;
v___y_362_ = v___y_371_;
v___y_363_ = v___y_373_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_380_;
v___y_368_ = v___x_382_;
v___y_369_ = v___y_371_;
goto v___jp_355_;
}
else
{
v___y_356_ = v___y_372_;
v___y_357_ = v___y_374_;
v___y_358_ = v___y_376_;
v___y_359_ = v___x_385_;
v___y_360_ = v___y_379_;
v___y_361_ = v___y_381_;
v___y_362_ = v___y_371_;
v___y_363_ = v___y_373_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_380_;
v___y_368_ = v___x_382_;
v___y_369_ = v___y_376_;
goto v___jp_355_;
}
}
v___jp_390_:
{
lean_object* v_toCold_403_; lean_object* v_currRecDepth_404_; lean_object* v_ref_405_; uint8_t v_suppressElabErrors_406_; uint8_t v_isRecordingDeps_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_437_; 
v_toCold_403_ = lean_ctor_get(v___y_401_, 0);
v_currRecDepth_404_ = lean_ctor_get(v___y_401_, 1);
v_ref_405_ = lean_ctor_get(v___y_401_, 2);
v_suppressElabErrors_406_ = lean_ctor_get_uint8(v___y_401_, sizeof(void*)*3 + 2);
v_isRecordingDeps_407_ = lean_ctor_get_uint8(v___y_401_, sizeof(void*)*3 + 3);
v_isSharedCheck_437_ = !lean_is_exclusive(v___y_401_);
if (v_isSharedCheck_437_ == 0)
{
v___x_409_ = v___y_401_;
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_ref_405_);
lean_inc(v_currRecDepth_404_);
lean_inc(v_toCold_403_);
lean_dec(v___y_401_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_fileName_411_; lean_object* v_fileMap_412_; lean_object* v_currNamespace_413_; lean_object* v_openDecls_414_; lean_object* v_initHeartbeats_415_; lean_object* v_maxHeartbeats_416_; lean_object* v_quotContext_417_; lean_object* v_currMacroScope_418_; lean_object* v_cancelTk_x3f_419_; lean_object* v_inheritedTraceOptions_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_434_; 
v_fileName_411_ = lean_ctor_get(v_toCold_403_, 0);
v_fileMap_412_ = lean_ctor_get(v_toCold_403_, 1);
v_currNamespace_413_ = lean_ctor_get(v_toCold_403_, 4);
v_openDecls_414_ = lean_ctor_get(v_toCold_403_, 5);
v_initHeartbeats_415_ = lean_ctor_get(v_toCold_403_, 6);
v_maxHeartbeats_416_ = lean_ctor_get(v_toCold_403_, 7);
v_quotContext_417_ = lean_ctor_get(v_toCold_403_, 8);
v_currMacroScope_418_ = lean_ctor_get(v_toCold_403_, 9);
v_cancelTk_x3f_419_ = lean_ctor_get(v_toCold_403_, 10);
v_inheritedTraceOptions_420_ = lean_ctor_get(v_toCold_403_, 11);
v_isSharedCheck_434_ = !lean_is_exclusive(v_toCold_403_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_435_ = lean_ctor_get(v_toCold_403_, 3);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_toCold_403_, 2);
lean_dec(v_unused_436_);
v___x_422_ = v_toCold_403_;
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_inheritedTraceOptions_420_);
lean_inc(v_cancelTk_x3f_419_);
lean_inc(v_currMacroScope_418_);
lean_inc(v_quotContext_417_);
lean_inc(v_maxHeartbeats_416_);
lean_inc(v_initHeartbeats_415_);
lean_inc(v_openDecls_414_);
lean_inc(v_currNamespace_413_);
lean_inc(v_fileMap_412_);
lean_inc(v_fileName_411_);
lean_dec(v_toCold_403_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_400_, v___y_397_);
lean_inc_ref(v___y_400_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 3, v___x_424_);
lean_ctor_set(v___x_422_, 2, v___y_400_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fileName_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_fileMap_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v___y_400_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_currNamespace_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_openDecls_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_initHeartbeats_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_maxHeartbeats_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_quotContext_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_currMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_cancelTk_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 11, v_inheritedTraceOptions_420_);
v___x_426_ = v_reuseFailAlloc_433_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_426_);
v___x_428_ = v___x_409_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_currRecDepth_404_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_ref_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 2, v_suppressElabErrors_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 3, v_isRecordingDeps_407_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_ctor_set_uint16(v___x_428_, sizeof(void*)*3, v___y_399_);
if (v_isRecordingDeps_407_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_430_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_400_, v___x_429_, v___y_391_);
v___y_371_ = v___y_391_;
v___y_372_ = v___y_392_;
v___y_373_ = v___y_393_;
v___y_374_ = v___y_394_;
v___y_375_ = v___y_402_;
v___y_376_ = v___y_395_;
v___y_377_ = v___y_396_;
v___y_378_ = v___x_428_;
v___y_379_ = v___y_397_;
v___y_380_ = v___y_398_;
v___y_381_ = v___x_430_;
goto v___jp_370_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_400_);
v___y_371_ = v___y_391_;
v___y_372_ = v___y_392_;
v___y_373_ = v___y_393_;
v___y_374_ = v___y_394_;
v___y_375_ = v___y_402_;
v___y_376_ = v___y_395_;
v___y_377_ = v___y_396_;
v___y_378_ = v___x_428_;
v___y_379_ = v___y_397_;
v___y_380_ = v___y_398_;
v___y_381_ = v___x_431_;
goto v___jp_370_;
}
}
}
}
}
}
v___jp_438_:
{
lean_object* v___x_452_; lean_object* v_env_453_; lean_object* v_nextMacroScope_454_; lean_object* v_ngen_455_; lean_object* v_auxDeclNGen_456_; lean_object* v_traceState_457_; lean_object* v_recordedDeps_458_; lean_object* v_messages_459_; lean_object* v_infoState_460_; lean_object* v_snapshotTasks_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
v___x_452_ = lean_st_ref_take(v___y_449_);
v_env_453_ = lean_ctor_get(v___x_452_, 0);
v_nextMacroScope_454_ = lean_ctor_get(v___x_452_, 1);
v_ngen_455_ = lean_ctor_get(v___x_452_, 2);
v_auxDeclNGen_456_ = lean_ctor_get(v___x_452_, 3);
v_traceState_457_ = lean_ctor_get(v___x_452_, 4);
v_recordedDeps_458_ = lean_ctor_get(v___x_452_, 6);
v_messages_459_ = lean_ctor_get(v___x_452_, 7);
v_infoState_460_ = lean_ctor_get(v___x_452_, 8);
v_snapshotTasks_461_ = lean_ctor_get(v___x_452_, 9);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_452_, 5);
lean_dec(v_unused_471_);
v___x_463_ = v___x_452_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_snapshotTasks_461_);
lean_inc(v_infoState_460_);
lean_inc(v_messages_459_);
lean_inc(v_recordedDeps_458_);
lean_inc(v_traceState_457_);
lean_inc(v_auxDeclNGen_456_);
lean_inc(v_ngen_455_);
lean_inc(v_nextMacroScope_454_);
lean_inc(v_env_453_);
lean_dec(v___x_452_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = l_Lean_Kernel_enableDiag(v_env_453_, v___y_439_);
lean_inc_ref(v___y_441_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 5, v___y_441_);
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_nextMacroScope_454_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_ngen_455_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_auxDeclNGen_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_traceState_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v___y_441_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_recordedDeps_458_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_messages_459_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_infoState_460_);
lean_ctor_set(v_reuseFailAlloc_469_, 9, v_snapshotTasks_461_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_st_ref_put(v___y_449_, v___x_467_);
v___y_391_ = v___y_445_;
v___y_392_ = v___y_440_;
v___y_393_ = v___y_446_;
v___y_394_ = v___y_441_;
v___y_395_ = v___y_443_;
v___y_396_ = v___y_447_;
v___y_397_ = v___y_444_;
v___y_398_ = v___y_448_;
v___y_399_ = v___y_451_;
v___y_400_ = v___y_450_;
v___y_401_ = v___y_442_;
v___y_402_ = v___y_449_;
goto v___jp_390_;
}
}
}
v___jp_472_:
{
if (v___y_486_ == 0)
{
if (v___y_481_ == 0)
{
v___y_391_ = v___y_478_;
v___y_392_ = v___y_473_;
v___y_393_ = v___y_479_;
v___y_394_ = v___y_474_;
v___y_395_ = v___y_476_;
v___y_396_ = v___y_480_;
v___y_397_ = v___y_477_;
v___y_398_ = v___y_482_;
v___y_399_ = v___y_485_;
v___y_400_ = v___y_484_;
v___y_401_ = v___y_475_;
v___y_402_ = v___y_483_;
goto v___jp_390_;
}
else
{
v___y_439_ = v___y_486_;
v___y_440_ = v___y_473_;
v___y_441_ = v___y_474_;
v___y_442_ = v___y_475_;
v___y_443_ = v___y_476_;
v___y_444_ = v___y_477_;
v___y_445_ = v___y_478_;
v___y_446_ = v___y_479_;
v___y_447_ = v___y_480_;
v___y_448_ = v___y_482_;
v___y_449_ = v___y_483_;
v___y_450_ = v___y_484_;
v___y_451_ = v___y_485_;
goto v___jp_438_;
}
}
else
{
if (v___y_481_ == 0)
{
v___y_439_ = v___y_486_;
v___y_440_ = v___y_473_;
v___y_441_ = v___y_474_;
v___y_442_ = v___y_475_;
v___y_443_ = v___y_476_;
v___y_444_ = v___y_477_;
v___y_445_ = v___y_478_;
v___y_446_ = v___y_479_;
v___y_447_ = v___y_480_;
v___y_448_ = v___y_482_;
v___y_449_ = v___y_483_;
v___y_450_ = v___y_484_;
v___y_451_ = v___y_485_;
goto v___jp_438_;
}
else
{
v___y_391_ = v___y_478_;
v___y_392_ = v___y_473_;
v___y_393_ = v___y_479_;
v___y_394_ = v___y_474_;
v___y_395_ = v___y_476_;
v___y_396_ = v___y_480_;
v___y_397_ = v___y_477_;
v___y_398_ = v___y_482_;
v___y_399_ = v___y_485_;
v___y_400_ = v___y_484_;
v___y_401_ = v___y_475_;
v___y_402_ = v___y_483_;
goto v___jp_390_;
}
}
}
v___jp_487_:
{
uint16_t v___x_499_; lean_object* v___x_500_; lean_object* v_env_501_; uint8_t v___x_502_; uint16_t v___x_503_; uint16_t v___x_504_; uint16_t v___x_505_; uint8_t v___x_506_; 
v___x_499_ = l_Lean_OptionFlags_ofOptions(v___y_498_);
v___x_500_ = lean_st_ref_get(v___y_497_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_env_501_);
lean_dec(v___x_500_);
v___x_502_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_501_);
lean_dec_ref(v_env_501_);
v___x_503_ = 512;
v___x_504_ = lean_uint16_land(v___x_499_, v___x_503_);
v___x_505_ = 0;
v___x_506_ = lean_uint16_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
v___y_473_ = v___y_489_;
v___y_474_ = v___y_492_;
v___y_475_ = v___y_491_;
v___y_476_ = v___y_493_;
v___y_477_ = v___y_495_;
v___y_478_ = v___y_488_;
v___y_479_ = v___y_490_;
v___y_480_ = v___y_494_;
v___y_481_ = v___x_502_;
v___y_482_ = v___y_496_;
v___y_483_ = v___y_497_;
v___y_484_ = v___y_498_;
v___y_485_ = v___x_499_;
v___y_486_ = v___y_488_;
goto v___jp_472_;
}
else
{
v___y_473_ = v___y_489_;
v___y_474_ = v___y_492_;
v___y_475_ = v___y_491_;
v___y_476_ = v___y_493_;
v___y_477_ = v___y_495_;
v___y_478_ = v___y_488_;
v___y_479_ = v___y_490_;
v___y_480_ = v___y_494_;
v___y_481_ = v___x_502_;
v___y_482_ = v___y_496_;
v___y_483_ = v___y_497_;
v___y_484_ = v___y_498_;
v___y_485_ = v___x_499_;
v___y_486_ = v___y_493_;
goto v___jp_472_;
}
}
v___jp_507_:
{
lean_object* v_toCold_519_; lean_object* v_currRecDepth_520_; lean_object* v_ref_521_; uint8_t v_suppressElabErrors_522_; uint8_t v_isRecordingDeps_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_554_; 
v_toCold_519_ = lean_ctor_get(v___y_517_, 0);
v_currRecDepth_520_ = lean_ctor_get(v___y_517_, 1);
v_ref_521_ = lean_ctor_get(v___y_517_, 2);
v_suppressElabErrors_522_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*3 + 2);
v_isRecordingDeps_523_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*3 + 3);
v_isSharedCheck_554_ = !lean_is_exclusive(v___y_517_);
if (v_isSharedCheck_554_ == 0)
{
v___x_525_ = v___y_517_;
v_isShared_526_ = v_isSharedCheck_554_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_ref_521_);
lean_inc(v_currRecDepth_520_);
lean_inc(v_toCold_519_);
lean_dec(v___y_517_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_554_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_fileName_527_; lean_object* v_fileMap_528_; lean_object* v_currNamespace_529_; lean_object* v_openDecls_530_; lean_object* v_initHeartbeats_531_; lean_object* v_maxHeartbeats_532_; lean_object* v_quotContext_533_; lean_object* v_currMacroScope_534_; lean_object* v_cancelTk_x3f_535_; lean_object* v_inheritedTraceOptions_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_551_; 
v_fileName_527_ = lean_ctor_get(v_toCold_519_, 0);
v_fileMap_528_ = lean_ctor_get(v_toCold_519_, 1);
v_currNamespace_529_ = lean_ctor_get(v_toCold_519_, 4);
v_openDecls_530_ = lean_ctor_get(v_toCold_519_, 5);
v_initHeartbeats_531_ = lean_ctor_get(v_toCold_519_, 6);
v_maxHeartbeats_532_ = lean_ctor_get(v_toCold_519_, 7);
v_quotContext_533_ = lean_ctor_get(v_toCold_519_, 8);
v_currMacroScope_534_ = lean_ctor_get(v_toCold_519_, 9);
v_cancelTk_x3f_535_ = lean_ctor_get(v_toCold_519_, 10);
v_inheritedTraceOptions_536_ = lean_ctor_get(v_toCold_519_, 11);
v_isSharedCheck_551_ = !lean_is_exclusive(v_toCold_519_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; lean_object* v_unused_553_; 
v_unused_552_ = lean_ctor_get(v_toCold_519_, 3);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_toCold_519_, 2);
lean_dec(v_unused_553_);
v___x_538_ = v_toCold_519_;
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_inheritedTraceOptions_536_);
lean_inc(v_cancelTk_x3f_535_);
lean_inc(v_currMacroScope_534_);
lean_inc(v_quotContext_533_);
lean_inc(v_maxHeartbeats_532_);
lean_inc(v_initHeartbeats_531_);
lean_inc(v_openDecls_530_);
lean_inc(v_currNamespace_529_);
lean_inc(v_fileMap_528_);
lean_inc(v_fileName_527_);
lean_dec(v_toCold_519_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = l_Lean_maxRecDepth;
v___x_541_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_516_, v___x_540_);
lean_inc_ref(v___y_516_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 3, v___x_541_);
lean_ctor_set(v___x_538_, 2, v___y_516_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fileName_527_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_fileMap_528_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___y_516_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_currNamespace_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_openDecls_530_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_initHeartbeats_531_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_maxHeartbeats_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_quotContext_533_);
lean_ctor_set(v_reuseFailAlloc_550_, 9, v_currMacroScope_534_);
lean_ctor_set(v_reuseFailAlloc_550_, 10, v_cancelTk_x3f_535_);
lean_ctor_set(v_reuseFailAlloc_550_, 11, v_inheritedTraceOptions_536_);
v___x_543_ = v_reuseFailAlloc_550_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_543_);
v___x_545_ = v___x_525_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_currRecDepth_520_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_ref_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*3 + 2, v_suppressElabErrors_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*3 + 3, v_isRecordingDeps_523_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_ctor_set_uint16(v___x_545_, sizeof(void*)*3, v___y_514_);
if (v_isRecordingDeps_523_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_547_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_516_, v___x_546_, v_isRecordingDeps_523_);
v___y_488_ = v___y_508_;
v___y_489_ = v___y_509_;
v___y_490_ = v___y_510_;
v___y_491_ = v___x_545_;
v___y_492_ = v___y_511_;
v___y_493_ = v___y_512_;
v___y_494_ = v___y_513_;
v___y_495_ = v___x_540_;
v___y_496_ = v___y_515_;
v___y_497_ = v___y_518_;
v___y_498_ = v___x_547_;
goto v___jp_487_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_516_);
v___y_488_ = v___y_508_;
v___y_489_ = v___y_509_;
v___y_490_ = v___y_510_;
v___y_491_ = v___x_545_;
v___y_492_ = v___y_511_;
v___y_493_ = v___y_512_;
v___y_494_ = v___y_513_;
v___y_495_ = v___x_540_;
v___y_496_ = v___y_515_;
v___y_497_ = v___y_518_;
v___y_498_ = v___x_548_;
goto v___jp_487_;
}
}
}
}
}
}
v___jp_555_:
{
lean_object* v___x_568_; lean_object* v_env_569_; lean_object* v_nextMacroScope_570_; lean_object* v_ngen_571_; lean_object* v_auxDeclNGen_572_; lean_object* v_traceState_573_; lean_object* v_recordedDeps_574_; lean_object* v_messages_575_; lean_object* v_infoState_576_; lean_object* v_snapshotTasks_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_586_; 
v___x_568_ = lean_st_ref_take(v___y_562_);
v_env_569_ = lean_ctor_get(v___x_568_, 0);
v_nextMacroScope_570_ = lean_ctor_get(v___x_568_, 1);
v_ngen_571_ = lean_ctor_get(v___x_568_, 2);
v_auxDeclNGen_572_ = lean_ctor_get(v___x_568_, 3);
v_traceState_573_ = lean_ctor_get(v___x_568_, 4);
v_recordedDeps_574_ = lean_ctor_get(v___x_568_, 6);
v_messages_575_ = lean_ctor_get(v___x_568_, 7);
v_infoState_576_ = lean_ctor_get(v___x_568_, 8);
v_snapshotTasks_577_ = lean_ctor_get(v___x_568_, 9);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_568_, 5);
lean_dec(v_unused_587_);
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_586_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snapshotTasks_577_);
lean_inc(v_infoState_576_);
lean_inc(v_messages_575_);
lean_inc(v_recordedDeps_574_);
lean_inc(v_traceState_573_);
lean_inc(v_auxDeclNGen_572_);
lean_inc(v_ngen_571_);
lean_inc(v_nextMacroScope_570_);
lean_inc(v_env_569_);
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_586_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_Kernel_enableDiag(v_env_569_, v___y_563_);
lean_inc_ref(v___y_557_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 5, v___y_557_);
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_nextMacroScope_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_ngen_571_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_auxDeclNGen_572_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_traceState_573_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v___y_557_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_recordedDeps_574_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_messages_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_585_, 9, v_snapshotTasks_577_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_st_ref_put(v___y_562_, v___x_583_);
v___y_508_ = v___y_560_;
v___y_509_ = v___y_556_;
v___y_510_ = v___y_561_;
v___y_511_ = v___y_557_;
v___y_512_ = v___y_558_;
v___y_513_ = v___y_564_;
v___y_514_ = v___y_559_;
v___y_515_ = v___y_565_;
v___y_516_ = v___y_566_;
v___y_517_ = v___y_567_;
v___y_518_ = v___y_562_;
goto v___jp_507_;
}
}
}
v___jp_588_:
{
if (v___y_601_ == 0)
{
if (v___y_592_ == 0)
{
v___y_508_ = v___y_594_;
v___y_509_ = v___y_589_;
v___y_510_ = v___y_595_;
v___y_511_ = v___y_590_;
v___y_512_ = v___y_591_;
v___y_513_ = v___y_597_;
v___y_514_ = v___y_593_;
v___y_515_ = v___y_598_;
v___y_516_ = v___y_599_;
v___y_517_ = v___y_600_;
v___y_518_ = v___y_596_;
goto v___jp_507_;
}
else
{
v___y_556_ = v___y_589_;
v___y_557_ = v___y_590_;
v___y_558_ = v___y_591_;
v___y_559_ = v___y_593_;
v___y_560_ = v___y_594_;
v___y_561_ = v___y_595_;
v___y_562_ = v___y_596_;
v___y_563_ = v___y_601_;
v___y_564_ = v___y_597_;
v___y_565_ = v___y_598_;
v___y_566_ = v___y_599_;
v___y_567_ = v___y_600_;
goto v___jp_555_;
}
}
else
{
if (v___y_592_ == 0)
{
v___y_556_ = v___y_589_;
v___y_557_ = v___y_590_;
v___y_558_ = v___y_591_;
v___y_559_ = v___y_593_;
v___y_560_ = v___y_594_;
v___y_561_ = v___y_595_;
v___y_562_ = v___y_596_;
v___y_563_ = v___y_601_;
v___y_564_ = v___y_597_;
v___y_565_ = v___y_598_;
v___y_566_ = v___y_599_;
v___y_567_ = v___y_600_;
goto v___jp_555_;
}
else
{
v___y_508_ = v___y_594_;
v___y_509_ = v___y_589_;
v___y_510_ = v___y_595_;
v___y_511_ = v___y_590_;
v___y_512_ = v___y_591_;
v___y_513_ = v___y_597_;
v___y_514_ = v___y_593_;
v___y_515_ = v___y_598_;
v___y_516_ = v___y_599_;
v___y_517_ = v___y_600_;
v___y_518_ = v___y_596_;
goto v___jp_507_;
}
}
}
v___jp_602_:
{
uint16_t v___x_613_; lean_object* v___x_614_; lean_object* v_env_615_; uint8_t v___x_616_; uint16_t v___x_617_; uint16_t v___x_618_; uint16_t v___x_619_; uint8_t v___x_620_; 
v___x_613_ = l_Lean_OptionFlags_ofOptions(v___y_612_);
v___x_614_ = lean_st_ref_get(v___y_607_);
v_env_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_615_);
lean_dec(v___x_614_);
v___x_616_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_615_);
lean_dec_ref(v_env_615_);
v___x_617_ = 512;
v___x_618_ = lean_uint16_land(v___x_613_, v___x_617_);
v___x_619_ = 0;
v___x_620_ = lean_uint16_dec_eq(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
v___y_589_ = v___y_604_;
v___y_590_ = v___y_606_;
v___y_591_ = v___y_608_;
v___y_592_ = v___x_616_;
v___y_593_ = v___x_613_;
v___y_594_ = v___y_603_;
v___y_595_ = v___y_605_;
v___y_596_ = v___y_607_;
v___y_597_ = v___y_609_;
v___y_598_ = v___y_610_;
v___y_599_ = v___y_612_;
v___y_600_ = v___y_611_;
v___y_601_ = v___y_603_;
goto v___jp_588_;
}
else
{
v___y_589_ = v___y_604_;
v___y_590_ = v___y_606_;
v___y_591_ = v___y_608_;
v___y_592_ = v___x_616_;
v___y_593_ = v___x_613_;
v___y_594_ = v___y_603_;
v___y_595_ = v___y_605_;
v___y_596_ = v___y_607_;
v___y_597_ = v___y_609_;
v___y_598_ = v___y_610_;
v___y_599_ = v___y_612_;
v___y_600_ = v___y_611_;
v___y_601_ = v___y_608_;
goto v___jp_588_;
}
}
v___jp_621_:
{
lean_object* v___x_630_; 
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc_ref(v___y_623_);
v___x_630_ = lean_infer_type(v___y_623_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_n(v_a_631_, 2);
lean_dec_ref_known(v___x_630_, 1);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
v___x_632_ = lean_apply_6(v_checkType_259_, v_a_631_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, lean_box(0));
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_env_640_; lean_object* v_nextMacroScope_641_; lean_object* v_ngen_642_; lean_object* v_auxDeclNGen_643_; lean_object* v_traceState_644_; lean_object* v_recordedDeps_645_; lean_object* v_messages_646_; lean_object* v_infoState_647_; lean_object* v_snapshotTasks_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref_known(v___x_632_, 1);
v___x_633_ = lean_array_to_list(v___y_625_);
lean_inc_n(v___y_624_, 2);
v___x_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_634_, 0, v___y_624_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v_a_631_);
v___x_635_ = lean_box(0);
lean_inc(v___y_622_);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_624_);
lean_ctor_set(v___x_636_, 1, v___y_622_);
v___x_637_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___y_623_);
lean_ctor_set(v___x_637_, 2, v___x_635_);
lean_ctor_set(v___x_637_, 3, v___x_636_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*4, v_safety_260_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___x_639_ = lean_st_ref_take(v___y_629_);
v_env_640_ = lean_ctor_get(v___x_639_, 0);
v_nextMacroScope_641_ = lean_ctor_get(v___x_639_, 1);
v_ngen_642_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_643_ = lean_ctor_get(v___x_639_, 3);
v_traceState_644_ = lean_ctor_get(v___x_639_, 4);
v_recordedDeps_645_ = lean_ctor_get(v___x_639_, 6);
v_messages_646_ = lean_ctor_get(v___x_639_, 7);
v_infoState_647_ = lean_ctor_get(v___x_639_, 8);
v_snapshotTasks_648_ = lean_ctor_get(v___x_639_, 9);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_639_, 5);
lean_dec(v_unused_695_);
v___x_650_ = v___x_639_;
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_snapshotTasks_648_);
lean_inc(v_infoState_647_);
lean_inc(v_messages_646_);
lean_inc(v_recordedDeps_645_);
lean_inc(v_traceState_644_);
lean_inc(v_auxDeclNGen_643_);
lean_inc(v_ngen_642_);
lean_inc(v_nextMacroScope_641_);
lean_inc(v_env_640_);
lean_dec(v___x_639_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
lean_inc(v___y_624_);
v___x_652_ = l_Lean_markMeta(v_env_640_, v___y_624_);
v___x_653_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 5, v___x_653_);
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_655_ = v___x_650_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_nextMacroScope_641_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_ngen_642_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_auxDeclNGen_643_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_traceState_644_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_693_, 6, v_recordedDeps_645_);
lean_ctor_set(v_reuseFailAlloc_693_, 7, v_messages_646_);
lean_ctor_set(v_reuseFailAlloc_693_, 8, v_infoState_647_);
lean_ctor_set(v_reuseFailAlloc_693_, 9, v_snapshotTasks_648_);
v___x_655_ = v_reuseFailAlloc_693_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_mctx_658_; lean_object* v_zetaDeltaFVarIds_659_; lean_object* v_postponed_660_; lean_object* v_diag_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_691_; 
v___x_656_ = lean_st_ref_put(v___y_629_, v___x_655_);
v___x_657_ = lean_st_ref_take(v___y_627_);
v_mctx_658_ = lean_ctor_get(v___x_657_, 0);
v_zetaDeltaFVarIds_659_ = lean_ctor_get(v___x_657_, 2);
v_postponed_660_ = lean_ctor_get(v___x_657_, 3);
v_diag_661_ = lean_ctor_get(v___x_657_, 4);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_657_, 1);
lean_dec(v_unused_692_);
v___x_663_ = v___x_657_;
v_isShared_664_ = v_isSharedCheck_691_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_diag_661_);
lean_inc(v_postponed_660_);
lean_inc(v_zetaDeltaFVarIds_659_);
lean_inc(v_mctx_658_);
lean_dec(v___x_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_691_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_mctx_658_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_zetaDeltaFVarIds_659_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_postponed_660_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_diag_661_);
v___x_667_ = v_reuseFailAlloc_690_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_env_670_; lean_object* v_checked_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_668_ = lean_st_ref_put(v___y_627_, v___x_667_);
v___x_669_ = lean_st_ref_get(v___y_629_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v_checked_671_ = lean_ctor_get(v_env_670_, 2);
lean_inc_ref(v_checked_671_);
lean_dec_ref(v_env_670_);
v___x_672_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_673_ = l_Lean_traceBlock___redArg(v___x_672_, v_checked_671_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_toCold_674_; uint8_t v_isRecordingDeps_675_; lean_object* v_options_676_; uint8_t v___x_677_; uint8_t v___x_678_; 
lean_dec_ref_known(v___x_673_, 1);
v_toCold_674_ = lean_ctor_get(v___y_628_, 0);
v_isRecordingDeps_675_ = lean_ctor_get_uint8(v___y_628_, sizeof(void*)*3 + 3);
v_options_676_ = lean_ctor_get(v_toCold_674_, 2);
v___x_677_ = 1;
v___x_678_ = 0;
if (v_isRecordingDeps_675_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Lean_Elab_async;
lean_inc_ref(v_options_676_);
v___x_680_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_options_676_, v___x_679_, v_isRecordingDeps_675_);
v___y_603_ = v___x_677_;
v___y_604_ = v___x_638_;
v___y_605_ = v___y_626_;
v___y_606_ = v___x_653_;
v___y_607_ = v___y_629_;
v___y_608_ = v___x_678_;
v___y_609_ = v___y_627_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_628_;
v___y_612_ = v___x_680_;
goto v___jp_602_;
}
else
{
lean_object* v___x_681_; 
lean_inc_ref(v_options_676_);
v___x_681_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_676_);
v___y_603_ = v___x_677_;
v___y_604_ = v___x_638_;
v___y_605_ = v___y_626_;
v___y_606_ = v___x_653_;
v___y_607_ = v___y_629_;
v___y_608_ = v___x_678_;
v___y_609_ = v___y_627_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_628_;
v___y_612_ = v___x_681_;
goto v___jp_602_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref_known(v___x_638_, 1);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_624_);
v_a_682_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
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
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_a_631_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
v_a_696_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_632_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_632_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_checkType_259_);
v_a_704_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_630_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_630_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v_env_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = lean_st_ref_get(v___y_265_);
v_env_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_env_714_);
lean_dec(v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_716_ = l_Lean_Core_mkFreshUserName(v___x_715_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_mkPrivateName(v_env_714_, v_a_717_);
lean_dec_ref(v_env_714_);
v___x_719_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_261_, v___y_263_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_params_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_n(v_a_720_, 2);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_722_ = l_Lean_collectLevelParams(v___x_721_, v_a_720_);
v_params_723_ = lean_ctor_get(v___x_722_, 2);
lean_inc_ref(v_params_723_);
lean_dec_ref(v___x_722_);
v___x_724_ = lean_box(0);
v___x_725_ = l_Lean_Expr_hasMVar(v_a_720_);
if (v___x_725_ == 0)
{
v___y_622_ = v___x_724_;
v___y_623_ = v_a_720_;
v___y_624_ = v___x_718_;
v___y_625_ = v_params_723_;
v___y_626_ = v___y_262_;
v___y_627_ = v___y_263_;
v___y_628_ = v___y_264_;
v___y_629_ = v___y_265_;
goto v___jp_621_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_720_);
v___x_727_ = l_Lean_indentExpr(v_a_720_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_728_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref_known(v___x_729_, 1);
v___y_622_ = v___x_724_;
v___y_623_ = v_a_720_;
v___y_624_ = v___x_718_;
v___y_625_ = v_params_723_;
v___y_626_ = v___y_262_;
v___y_627_ = v___y_263_;
v___y_628_ = v___y_264_;
v___y_629_ = v___y_265_;
goto v___jp_621_;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_params_723_);
lean_dec(v_a_720_);
lean_dec(v___x_718_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_checkType_259_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___x_718_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_checkType_259_);
v_a_738_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_719_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_719_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_env_714_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_value_261_);
lean_dec_ref(v_checkType_259_);
v_a_746_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_716_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_716_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
v___jp_754_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_mctx_768_; lean_object* v_zetaDeltaFVarIds_769_; lean_object* v_postponed_770_; lean_object* v_diag_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_780_; 
v___x_764_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_765_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_765_, 0, v___y_763_);
lean_ctor_set(v___x_765_, 1, v_nextMacroScope_755_);
lean_ctor_set(v___x_765_, 2, v_ngen_756_);
lean_ctor_set(v___x_765_, 3, v_auxDeclNGen_757_);
lean_ctor_set(v___x_765_, 4, v_traceState_758_);
lean_ctor_set(v___x_765_, 5, v___x_764_);
lean_ctor_set(v___x_765_, 6, v_recordedDeps_759_);
lean_ctor_set(v___x_765_, 7, v_messages_760_);
lean_ctor_set(v___x_765_, 8, v_infoState_761_);
lean_ctor_set(v___x_765_, 9, v_snapshotTasks_762_);
v___x_766_ = lean_st_ref_put(v___y_265_, v___x_765_);
v___x_767_ = lean_st_ref_take(v___y_263_);
v_mctx_768_ = lean_ctor_get(v___x_767_, 0);
v_zetaDeltaFVarIds_769_ = lean_ctor_get(v___x_767_, 2);
v_postponed_770_ = lean_ctor_get(v___x_767_, 3);
v_diag_771_ = lean_ctor_get(v___x_767_, 4);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_767_, 1);
lean_dec(v_unused_781_);
v___x_773_ = v___x_767_;
v_isShared_774_ = v_isSharedCheck_780_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_diag_771_);
lean_inc(v_postponed_770_);
lean_inc(v_zetaDeltaFVarIds_769_);
lean_inc(v_mctx_768_);
lean_dec(v___x_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_780_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_mctx_768_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_zetaDeltaFVarIds_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_postponed_770_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_diag_771_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = lean_st_ref_put(v___y_263_, v___x_777_);
goto v___jp_712_;
}
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v_nextMacroScope_786_; lean_object* v_ngen_787_; lean_object* v_auxDeclNGen_788_; lean_object* v_traceState_789_; lean_object* v_recordedDeps_790_; lean_object* v_messages_791_; lean_object* v_infoState_792_; lean_object* v_snapshotTasks_793_; lean_object* v___x_794_; 
v___x_784_ = lean_st_ref_take(v___y_265_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref_n(v_env_785_, 2);
v_nextMacroScope_786_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_nextMacroScope_786_);
v_ngen_787_ = lean_ctor_get(v___x_784_, 2);
lean_inc_ref(v_ngen_787_);
v_auxDeclNGen_788_ = lean_ctor_get(v___x_784_, 3);
lean_inc_ref(v_auxDeclNGen_788_);
v_traceState_789_ = lean_ctor_get(v___x_784_, 4);
lean_inc_ref(v_traceState_789_);
v_recordedDeps_790_ = lean_ctor_get(v___x_784_, 6);
lean_inc_ref(v_recordedDeps_790_);
v_messages_791_ = lean_ctor_get(v___x_784_, 7);
lean_inc_ref(v_messages_791_);
v_infoState_792_ = lean_ctor_get(v___x_784_, 8);
lean_inc_ref(v_infoState_792_);
v_snapshotTasks_793_ = lean_ctor_get(v___x_784_, 9);
lean_inc_ref(v_snapshotTasks_793_);
lean_dec(v___x_784_);
v___x_794_ = l_Lean_Environment_importEnv_x3f(v_env_785_);
if (lean_obj_tag(v___x_794_) == 0)
{
v_nextMacroScope_755_ = v_nextMacroScope_786_;
v_ngen_756_ = v_ngen_787_;
v_auxDeclNGen_757_ = v_auxDeclNGen_788_;
v_traceState_758_ = v_traceState_789_;
v_recordedDeps_759_ = v_recordedDeps_790_;
v_messages_760_ = v_messages_791_;
v_infoState_761_ = v_infoState_792_;
v_snapshotTasks_762_ = v_snapshotTasks_793_;
v___y_763_ = v_env_785_;
goto v___jp_754_;
}
else
{
lean_object* v_val_795_; 
lean_dec_ref(v_env_785_);
v_val_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v___x_794_, 1);
v_nextMacroScope_755_ = v_nextMacroScope_786_;
v_ngen_756_ = v_ngen_787_;
v_auxDeclNGen_757_ = v_auxDeclNGen_788_;
v_traceState_758_ = v_traceState_789_;
v_recordedDeps_759_ = v_recordedDeps_790_;
v_messages_760_ = v_messages_791_;
v_infoState_761_ = v_infoState_792_;
v_snapshotTasks_762_ = v_snapshotTasks_793_;
v___y_763_ = v_val_795_;
goto v___jp_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_804_, lean_object* v_checkType_805_, lean_object* v_safety_806_, lean_object* v_value_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_checkMeta_boxed_813_; uint8_t v_safety_boxed_814_; lean_object* v_res_815_; 
v_checkMeta_boxed_813_ = lean_unbox(v_checkMeta_804_);
v_safety_boxed_814_ = lean_unbox(v_safety_806_);
v_res_815_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_813_, v_checkType_805_, v_safety_boxed_814_, v_value_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object* v_env_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_nextMacroScope_821_; lean_object* v_ngen_822_; lean_object* v_auxDeclNGen_823_; lean_object* v_traceState_824_; lean_object* v_recordedDeps_825_; lean_object* v_messages_826_; lean_object* v_infoState_827_; lean_object* v_snapshotTasks_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_854_; 
v___x_820_ = lean_st_ref_take(v___y_818_);
v_nextMacroScope_821_ = lean_ctor_get(v___x_820_, 1);
v_ngen_822_ = lean_ctor_get(v___x_820_, 2);
v_auxDeclNGen_823_ = lean_ctor_get(v___x_820_, 3);
v_traceState_824_ = lean_ctor_get(v___x_820_, 4);
v_recordedDeps_825_ = lean_ctor_get(v___x_820_, 6);
v_messages_826_ = lean_ctor_get(v___x_820_, 7);
v_infoState_827_ = lean_ctor_get(v___x_820_, 8);
v_snapshotTasks_828_ = lean_ctor_get(v___x_820_, 9);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v___x_820_, 5);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v___x_820_, 0);
lean_dec(v_unused_856_);
v___x_830_ = v___x_820_;
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_snapshotTasks_828_);
lean_inc(v_infoState_827_);
lean_inc(v_messages_826_);
lean_inc(v_recordedDeps_825_);
lean_inc(v_traceState_824_);
lean_inc(v_auxDeclNGen_823_);
lean_inc(v_ngen_822_);
lean_inc(v_nextMacroScope_821_);
lean_dec(v___x_820_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_854_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 5, v___x_832_);
lean_ctor_set(v___x_830_, 0, v_env_816_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_env_816_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_nextMacroScope_821_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_ngen_822_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_auxDeclNGen_823_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v_traceState_824_);
lean_ctor_set(v_reuseFailAlloc_853_, 5, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_853_, 6, v_recordedDeps_825_);
lean_ctor_set(v_reuseFailAlloc_853_, 7, v_messages_826_);
lean_ctor_set(v_reuseFailAlloc_853_, 8, v_infoState_827_);
lean_ctor_set(v_reuseFailAlloc_853_, 9, v_snapshotTasks_828_);
v___x_834_ = v_reuseFailAlloc_853_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_mctx_837_; lean_object* v_zetaDeltaFVarIds_838_; lean_object* v_postponed_839_; lean_object* v_diag_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v___x_835_ = lean_st_ref_put(v___y_818_, v___x_834_);
v___x_836_ = lean_st_ref_take(v___y_817_);
v_mctx_837_ = lean_ctor_get(v___x_836_, 0);
v_zetaDeltaFVarIds_838_ = lean_ctor_get(v___x_836_, 2);
v_postponed_839_ = lean_ctor_get(v___x_836_, 3);
v_diag_840_ = lean_ctor_get(v___x_836_, 4);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_836_, 1);
lean_dec(v_unused_852_);
v___x_842_ = v___x_836_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_diag_840_);
lean_inc(v_postponed_839_);
lean_inc(v_zetaDeltaFVarIds_838_);
lean_inc(v_mctx_837_);
lean_dec(v___x_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = lean_box(0);
v___x_845_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_mctx_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_zetaDeltaFVarIds_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_postponed_839_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_diag_840_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_st_ref_put(v___y_817_, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_844_);
return v___x_849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object* v_env_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object* v_env_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_env_870_; lean_object* v_a_872_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_869_ = lean_st_ref_get(v___y_867_);
v_env_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_env_870_);
lean_dec(v___x_869_);
v___x_882_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_862_, v___y_865_, v___y_867_);
lean_dec_ref(v___x_882_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_883_ = lean_apply_5(v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_870_, v___y_865_, v___y_867_);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_885_, 0);
lean_dec(v_unused_893_);
v___x_887_ = v___x_885_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_dec(v___x_885_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_a_884_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_884_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v_a_894_; 
v_a_894_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_883_, 1);
v_a_872_ = v_a_894_;
goto v___jp_871_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v___x_873_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_870_, v___y_865_, v___y_867_);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v___x_873_, 0);
lean_dec(v_unused_881_);
v___x_875_ = v___x_873_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_dec(v___x_873_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v_a_872_);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_872_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object* v_env_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_903_, lean_object* v_checkType_904_, uint8_t v_safety_905_, uint8_t v_checkMeta_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v_env_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_912_ = lean_box(v_checkMeta_906_);
v___x_913_ = lean_box(v_safety_905_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_914_, 0, v___x_912_);
lean_closure_set(v___f_914_, 1, v_checkType_904_);
lean_closure_set(v___f_914_, 2, v___x_913_);
lean_closure_set(v___f_914_, 3, v_value_903_);
v___x_915_ = lean_st_ref_get(v_a_910_);
v_env_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_env_916_);
lean_dec(v___x_915_);
v___x_917_ = l_Lean_Environment_unlockAsync(v_env_916_);
v___x_918_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v___x_917_, v___f_914_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_919_, lean_object* v_checkType_920_, lean_object* v_safety_921_, lean_object* v_checkMeta_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v_safety_boxed_928_; uint8_t v_checkMeta_boxed_929_; lean_object* v_res_930_; 
v_safety_boxed_928_ = lean_unbox(v_safety_921_);
v_checkMeta_boxed_929_ = lean_unbox(v_checkMeta_922_);
v_res_930_ = l_Lean_Meta_evalExprCore___redArg(v_value_919_, v_checkType_920_, v_safety_boxed_928_, v_checkMeta_boxed_929_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_931_, lean_object* v_value_932_, lean_object* v_checkType_933_, uint8_t v_safety_934_, uint8_t v_checkMeta_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_evalExprCore___redArg(v_value_932_, v_checkType_933_, v_safety_934_, v_checkMeta_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_942_, lean_object* v_value_943_, lean_object* v_checkType_944_, lean_object* v_safety_945_, lean_object* v_checkMeta_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_safety_boxed_952_; uint8_t v_checkMeta_boxed_953_; lean_object* v_res_954_; 
v_safety_boxed_952_ = lean_unbox(v_safety_945_);
v_checkMeta_boxed_953_ = lean_unbox(v_checkMeta_946_);
v_res_954_ = l_Lean_Meta_evalExprCore(v_00_u03b1_942_, v_value_943_, v_checkType_944_, v_safety_boxed_952_, v_checkMeta_boxed_953_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_object* v_00_u03b1_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___boxed(lean_object* v_00_u03b1_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(v_00_u03b1_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_00_u03b1_969_, lean_object* v_constName_970_, uint8_t v_checkMeta_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_970_, v_checkMeta_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_00_u03b1_978_, lean_object* v_constName_979_, lean_object* v_checkMeta_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v_checkMeta_boxed_986_; lean_object* v_res_987_; 
v_checkMeta_boxed_986_ = lean_unbox(v_checkMeta_980_);
v_res_987_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(v_00_u03b1_978_, v_constName_979_, v_checkMeta_boxed_986_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_988_, lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_996_, lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_996_, v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object* v_env_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_1004_, v___y_1006_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object* v_env_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v_00_u03b1_1018_, lean_object* v_env_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_1019_, v_x_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_env_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(v_00_u03b1_1027_, v_env_1028_, v_x_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_object* v_00_u03b1_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(v_00_u03b1_1044_, v_x_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1055_, lean_object* v_type_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_whnfD(v_type_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1076_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_Expr_isConstOf(v_a_1063_, v_typeName_1055_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_1065_);
v___x_1068_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1069_ = l_Lean_indentExpr(v_a_1063_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1070_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_dec(v_a_1063_);
v___x_1072_ = lean_box(0);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1072_);
v___x_1074_ = v___x_1065_;
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
v_a_1077_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1062_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1062_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1085_, lean_object* v_type_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1085_, v_type_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v_typeName_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1093_, lean_object* v_value_1094_, uint8_t v_safety_1095_, uint8_t v_checkMeta_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1102_, 0, v_typeName_1093_);
v___x_1103_ = l_Lean_Meta_evalExprCore___redArg(v_value_1094_, v___f_1102_, v_safety_1095_, v_checkMeta_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1104_, lean_object* v_value_1105_, lean_object* v_safety_1106_, lean_object* v_checkMeta_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v_safety_boxed_1113_; uint8_t v_checkMeta_boxed_1114_; lean_object* v_res_1115_; 
v_safety_boxed_1113_ = lean_unbox(v_safety_1106_);
v_checkMeta_boxed_1114_ = lean_unbox(v_checkMeta_1107_);
v_res_1115_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1104_, v_value_1105_, v_safety_boxed_1113_, v_checkMeta_boxed_1114_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1116_, lean_object* v_typeName_1117_, lean_object* v_value_1118_, uint8_t v_safety_1119_, uint8_t v_checkMeta_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1117_, v_value_1118_, v_safety_1119_, v_checkMeta_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_typeName_1128_, lean_object* v_value_1129_, lean_object* v_safety_1130_, lean_object* v_checkMeta_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
uint8_t v_safety_boxed_1137_; uint8_t v_checkMeta_boxed_1138_; lean_object* v_res_1139_; 
v_safety_boxed_1137_ = lean_unbox(v_safety_1130_);
v_checkMeta_boxed_1138_ = lean_unbox(v_checkMeta_1131_);
v_res_1139_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1127_, v_typeName_1128_, v_value_1129_, v_safety_boxed_1137_, v_checkMeta_boxed_1138_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1139_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1145_, lean_object* v_type_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
lean_inc_ref(v_expectedType_1145_);
lean_inc_ref(v_type_1146_);
v___x_1152_ = l_Lean_Meta_isExprDefEq(v_type_1146_, v_expectedType_1145_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1177_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_unbox(v_a_1153_);
lean_dec(v_a_1153_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_del_object(v___x_1155_);
v___x_1158_ = lean_box(0);
v___x_1159_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1160_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1146_, v_expectedType_1145_, v___x_1158_, v___x_1159_, v___y_1147_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_a_1161_);
v___x_1164_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1163_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1164_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1160_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1160_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec_ref(v_type_1146_);
lean_dec_ref(v_expectedType_1145_);
v___x_1173_ = lean_box(0);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1173_);
v___x_1175_ = v___x_1155_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_type_1146_);
lean_dec_ref(v_expectedType_1145_);
v_a_1178_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1152_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1152_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1186_, lean_object* v_type_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1186_, v_type_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1194_, lean_object* v_value_1195_, uint8_t v_safety_1196_, uint8_t v_checkMeta_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___f_1203_; lean_object* v___x_1204_; 
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1203_, 0, v_expectedType_1194_);
v___x_1204_ = l_Lean_Meta_evalExprCore___redArg(v_value_1195_, v___f_1203_, v_safety_1196_, v_checkMeta_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1205_, lean_object* v_value_1206_, lean_object* v_safety_1207_, lean_object* v_checkMeta_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
uint8_t v_safety_boxed_1214_; uint8_t v_checkMeta_boxed_1215_; lean_object* v_res_1216_; 
v_safety_boxed_1214_ = lean_unbox(v_safety_1207_);
v_checkMeta_boxed_1215_ = lean_unbox(v_checkMeta_1208_);
v_res_1216_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1205_, v_value_1206_, v_safety_boxed_1214_, v_checkMeta_boxed_1215_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1217_, lean_object* v_expectedType_1218_, lean_object* v_value_1219_, uint8_t v_safety_1220_, uint8_t v_checkMeta_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1218_, v_value_1219_, v_safety_1220_, v_checkMeta_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_expectedType_1229_, lean_object* v_value_1230_, lean_object* v_safety_1231_, lean_object* v_checkMeta_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
uint8_t v_safety_boxed_1238_; uint8_t v_checkMeta_boxed_1239_; lean_object* v_res_1240_; 
v_safety_boxed_1238_ = lean_unbox(v_safety_1231_);
v_checkMeta_boxed_1239_ = lean_unbox(v_checkMeta_1232_);
v_res_1240_ = l_Lean_Meta_evalExpr(v_00_u03b1_1228_, v_expectedType_1229_, v_value_1230_, v_safety_boxed_1238_, v_checkMeta_boxed_1239_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1240_;
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

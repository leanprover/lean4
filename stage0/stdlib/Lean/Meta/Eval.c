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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_93_; lean_object* v_env_94_; uint8_t v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v_toCold_98_; lean_object* v_mctx_99_; lean_object* v_lctx_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = 0;
v_env_96_ = l_Lean_Environment_setRecordingDeps(v_env_94_, v___x_95_);
v___x_97_ = lean_st_ref_get(v___y_89_);
v_toCold_98_ = lean_ctor_get(v___y_90_, 0);
v_mctx_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_mctx_99_);
lean_dec(v___x_97_);
v_lctx_100_ = lean_ctor_get(v___y_88_, 2);
v_options_101_ = lean_ctor_get(v_toCold_98_, 2);
lean_inc_ref(v_options_101_);
lean_inc_ref(v_lctx_100_);
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v_env_96_);
lean_ctor_set(v___x_102_, 1, v_mctx_99_);
lean_ctor_set(v___x_102_, 2, v_lctx_100_);
lean_ctor_set(v___x_102_, 3, v_options_101_);
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_msgData_87_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object* v_msgData_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msgData_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_msg_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 2);
v___x_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msg_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_128_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_ref_118_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_ref_118_);
lean_ctor_set(v___x_124_, 1, v_a_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 1);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(lean_object* v_x_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_a_142_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v_x_136_, 1);
v___x_143_ = l_Lean_stringToMessageData(v_a_142_);
v___x_144_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_143_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
return v___x_144_;
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v_x_136_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v_x_136_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v_x_136_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 0);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg___boxed(lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(lean_object* v_constName_160_, uint8_t v_checkMeta_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_env_168_; uint8_t v___x_169_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_env_168_);
lean_dec(v___x_167_);
lean_inc(v_constName_160_);
v___x_169_ = lean_has_compile_error(v_env_168_, v_constName_160_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v_env_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = lean_st_ref_get(v___y_165_);
v_env_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc_ref(v_env_171_);
lean_dec(v___x_170_);
v___x_172_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_164_);
v___x_173_ = l_Lean_Environment_evalConst___redArg(v_env_171_, v___x_172_, v_constName_160_, v_checkMeta_161_);
lean_dec(v_constName_160_);
lean_dec_ref(v___x_172_);
lean_dec_ref(v_env_171_);
v___x_174_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_173_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref_known(v___x_175_, 1);
v___x_176_ = lean_st_ref_get(v___y_165_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_176_);
v___x_178_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_164_);
v___x_179_ = l_Lean_Environment_evalConst___redArg(v_env_177_, v___x_178_, v_constName_160_, v_checkMeta_161_);
lean_dec(v_constName_160_);
lean_dec_ref(v___x_178_);
lean_dec_ref(v_env_177_);
v___x_180_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_179_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_180_;
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_constName_160_);
v_a_181_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_175_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_175_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg___boxed(lean_object* v_constName_189_, lean_object* v_checkMeta_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v_checkMeta_boxed_196_; lean_object* v_res_197_; 
v_checkMeta_boxed_196_ = lean_unbox(v_checkMeta_190_);
v_res_197_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_189_, v_checkMeta_boxed_196_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_o_201_, lean_object* v_k_202_, uint8_t v_v_203_){
_start:
{
lean_object* v_map_204_; uint8_t v_hasTrace_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_219_; 
v_map_204_ = lean_ctor_get(v_o_201_, 0);
v_hasTrace_205_ = lean_ctor_get_uint8(v_o_201_, sizeof(void*)*1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_o_201_);
if (v_isSharedCheck_219_ == 0)
{
v___x_207_ = v_o_201_;
v_isShared_208_ = v_isSharedCheck_219_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_map_204_);
lean_dec(v_o_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_219_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_209_, 0, v_v_203_);
lean_inc(v_k_202_);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_202_, v___x_209_, v_map_204_);
if (v_hasTrace_205_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_214_; 
v___x_211_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1));
v___x_212_ = l_Lean_Name_isPrefixOf(v___x_211_, v_k_202_);
lean_dec(v_k_202_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_210_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_212_);
return v___x_214_;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_k_202_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_217_ = v___x_207_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*1, v_hasTrace_205_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_o_220_, lean_object* v_k_221_, lean_object* v_v_222_){
_start:
{
uint8_t v_v_boxed_223_; lean_object* v_res_224_; 
v_v_boxed_223_ = lean_unbox(v_v_222_);
v_res_224_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_o_220_, v_k_221_, v_v_boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_opts_225_, lean_object* v_opt_226_, uint8_t v_val_227_){
_start:
{
lean_object* v_name_228_; lean_object* v___x_229_; 
v_name_228_ = lean_ctor_get(v_opt_226_, 0);
lean_inc(v_name_228_);
lean_dec_ref(v_opt_226_);
v___x_229_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_opts_225_, v_name_228_, v_val_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_opts_230_, lean_object* v_opt_231_, lean_object* v_val_232_){
_start:
{
uint8_t v_val_boxed_233_; lean_object* v_res_234_; 
v_val_boxed_233_ = lean_unbox(v_val_232_);
v_res_234_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_opts_230_, v_opt_231_, v_val_boxed_233_);
return v_res_234_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set(v___x_241_, 4, v___x_240_);
lean_ctor_set(v___x_241_, 5, v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_unsigned_to_nat(16u);
v___x_248_ = lean_mk_array(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_255_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set(v___x_256_, 2, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_260_, lean_object* v_checkType_261_, uint8_t v_safety_262_, lean_object* v_value_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___y_270_; uint8_t v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; uint16_t v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; uint8_t v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; uint16_t v___y_330_; lean_object* v___y_331_; uint8_t v___y_332_; uint8_t v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; uint16_t v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; uint8_t v___y_366_; lean_object* v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; uint8_t v___y_371_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; uint8_t v___y_396_; uint16_t v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; uint8_t v___y_448_; uint16_t v___y_449_; uint8_t v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; uint16_t v___y_482_; uint8_t v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; uint8_t v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; uint16_t v___y_513_; uint8_t v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint16_t v___y_563_; uint8_t v___y_564_; lean_object* v___y_565_; uint8_t v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; uint16_t v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; uint8_t v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v_nextMacroScope_757_; lean_object* v_ngen_758_; lean_object* v_auxDeclNGen_759_; lean_object* v_traceState_760_; lean_object* v_recordedDeps_761_; lean_object* v_messages_762_; lean_object* v_infoState_763_; lean_object* v_snapshotTasks_764_; lean_object* v___y_765_; lean_object* v___x_784_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_784_ = lean_st_ref_get(v___y_267_);
lean_inc_ref(v_value_263_);
v___x_798_ = l_Lean_Expr_getUsedConstants(v_value_263_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_array_get_size(v___x_798_);
v___x_801_ = lean_nat_dec_lt(v___x_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_dec_ref(v___x_798_);
lean_dec(v___x_784_);
goto v___jp_785_;
}
else
{
if (v___x_801_ == 0)
{
lean_dec_ref(v___x_798_);
lean_dec(v___x_784_);
goto v___jp_785_;
}
else
{
lean_object* v_env_802_; size_t v___x_803_; size_t v___x_804_; uint8_t v___x_805_; 
v_env_802_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_802_);
lean_dec(v___x_784_);
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_800_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v_env_802_, v___x_800_, v___x_798_, v___x_803_, v___x_804_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v_env_802_);
if (v___x_805_ == 0)
{
goto v___jp_785_;
}
else
{
goto v___jp_714_;
}
}
}
v___jp_269_:
{
lean_object* v_toCold_281_; lean_object* v_currRecDepth_282_; lean_object* v_ref_283_; uint8_t v_suppressElabErrors_284_; uint8_t v_isRecordingDeps_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_322_; 
v_toCold_281_ = lean_ctor_get(v___y_279_, 0);
v_currRecDepth_282_ = lean_ctor_get(v___y_279_, 1);
v_ref_283_ = lean_ctor_get(v___y_279_, 2);
v_suppressElabErrors_284_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 2);
v_isRecordingDeps_285_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 3);
v_isSharedCheck_322_ = !lean_is_exclusive(v___y_279_);
if (v_isSharedCheck_322_ == 0)
{
v___x_287_ = v___y_279_;
v_isShared_288_ = v_isSharedCheck_322_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_ref_283_);
lean_inc(v_currRecDepth_282_);
lean_inc(v_toCold_281_);
lean_dec(v___y_279_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_322_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_fileName_289_; lean_object* v_fileMap_290_; lean_object* v_currNamespace_291_; lean_object* v_openDecls_292_; lean_object* v_initHeartbeats_293_; lean_object* v_maxHeartbeats_294_; lean_object* v_quotContext_295_; lean_object* v_currMacroScope_296_; lean_object* v_cancelTk_x3f_297_; lean_object* v_inheritedTraceOptions_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_319_; 
v_fileName_289_ = lean_ctor_get(v_toCold_281_, 0);
v_fileMap_290_ = lean_ctor_get(v_toCold_281_, 1);
v_currNamespace_291_ = lean_ctor_get(v_toCold_281_, 4);
v_openDecls_292_ = lean_ctor_get(v_toCold_281_, 5);
v_initHeartbeats_293_ = lean_ctor_get(v_toCold_281_, 6);
v_maxHeartbeats_294_ = lean_ctor_get(v_toCold_281_, 7);
v_quotContext_295_ = lean_ctor_get(v_toCold_281_, 8);
v_currMacroScope_296_ = lean_ctor_get(v_toCold_281_, 9);
v_cancelTk_x3f_297_ = lean_ctor_get(v_toCold_281_, 10);
v_inheritedTraceOptions_298_ = lean_ctor_get(v_toCold_281_, 11);
v_isSharedCheck_319_ = !lean_is_exclusive(v_toCold_281_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v_toCold_281_, 3);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_toCold_281_, 2);
lean_dec(v_unused_321_);
v___x_300_ = v_toCold_281_;
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_inheritedTraceOptions_298_);
lean_inc(v_cancelTk_x3f_297_);
lean_inc(v_currMacroScope_296_);
lean_inc(v_quotContext_295_);
lean_inc(v_maxHeartbeats_294_);
lean_inc(v_initHeartbeats_293_);
lean_inc(v_openDecls_292_);
lean_inc(v_currNamespace_291_);
lean_inc(v_fileMap_290_);
lean_inc(v_fileName_289_);
lean_dec(v_toCold_281_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_275_, v___y_277_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 3, v___x_302_);
lean_ctor_set(v___x_300_, 2, v___y_275_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_fileName_289_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_fileMap_290_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v___y_275_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_currNamespace_291_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_openDecls_292_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_initHeartbeats_293_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_maxHeartbeats_294_);
lean_ctor_set(v_reuseFailAlloc_318_, 8, v_quotContext_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 9, v_currMacroScope_296_);
lean_ctor_set(v_reuseFailAlloc_318_, 10, v_cancelTk_x3f_297_);
lean_ctor_set(v_reuseFailAlloc_318_, 11, v_inheritedTraceOptions_298_);
v___x_304_ = v_reuseFailAlloc_318_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_304_);
v___x_306_ = v___x_287_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_currRecDepth_282_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_ref_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_317_, sizeof(void*)*3 + 2, v_suppressElabErrors_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_317_, sizeof(void*)*3 + 3, v_isRecordingDeps_285_);
v___x_306_ = v_reuseFailAlloc_317_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
lean_ctor_set_uint16(v___x_306_, sizeof(void*)*3, v___y_278_);
v___x_307_ = l_Lean_addAndCompile(v___y_274_, v___y_272_, v___y_271_, v___x_306_, v___y_280_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v___y_270_, v_checkMeta_260_, v___y_273_, v___y_276_, v___x_306_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___x_306_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_273_);
return v___x_308_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v___x_306_);
lean_dec(v___y_280_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_270_);
v_a_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
}
}
v___jp_323_:
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
v___x_337_ = lean_st_ref_take(v___y_326_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_recordedDeps_343_ = lean_ctor_get(v___x_337_, 6);
v_messages_344_ = lean_ctor_get(v___x_337_, 7);
v_infoState_345_ = lean_ctor_get(v___x_337_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_337_, 9);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_356_);
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_Kernel_enableDiag(v_env_338_, v___y_327_);
lean_inc_ref(v___y_331_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 5, v___y_331_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_354_, 5, v___y_331_);
lean_ctor_set(v_reuseFailAlloc_354_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_354_, 9, v_snapshotTasks_346_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_st_ref_put(v___y_326_, v___x_352_);
v___y_270_ = v___y_325_;
v___y_271_ = v___y_332_;
v___y_272_ = v___y_333_;
v___y_273_ = v___y_328_;
v___y_274_ = v___y_334_;
v___y_275_ = v___y_329_;
v___y_276_ = v___y_335_;
v___y_277_ = v___y_336_;
v___y_278_ = v___y_330_;
v___y_279_ = v___y_324_;
v___y_280_ = v___y_326_;
goto v___jp_269_;
}
}
}
v___jp_357_:
{
if (v___y_371_ == 0)
{
if (v___y_368_ == 0)
{
v___y_270_ = v___y_359_;
v___y_271_ = v___y_365_;
v___y_272_ = v___y_366_;
v___y_273_ = v___y_361_;
v___y_274_ = v___y_367_;
v___y_275_ = v___y_362_;
v___y_276_ = v___y_369_;
v___y_277_ = v___y_370_;
v___y_278_ = v___y_363_;
v___y_279_ = v___y_358_;
v___y_280_ = v___y_360_;
goto v___jp_269_;
}
else
{
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_371_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_366_;
v___y_334_ = v___y_367_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
goto v___jp_323_;
}
}
else
{
if (v___y_368_ == 0)
{
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_371_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_366_;
v___y_334_ = v___y_367_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
goto v___jp_323_;
}
else
{
v___y_270_ = v___y_359_;
v___y_271_ = v___y_365_;
v___y_272_ = v___y_366_;
v___y_273_ = v___y_361_;
v___y_274_ = v___y_367_;
v___y_275_ = v___y_362_;
v___y_276_ = v___y_369_;
v___y_277_ = v___y_370_;
v___y_278_ = v___y_363_;
v___y_279_ = v___y_358_;
v___y_280_ = v___y_360_;
goto v___jp_269_;
}
}
}
v___jp_372_:
{
uint16_t v___x_384_; lean_object* v___x_385_; lean_object* v_env_386_; uint8_t v___x_387_; uint16_t v___x_388_; uint16_t v___x_389_; uint16_t v___x_390_; uint8_t v___x_391_; 
v___x_384_ = l_Lean_OptionFlags_ofOptions(v___y_383_);
v___x_385_ = lean_st_ref_get(v___y_376_);
v_env_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_385_);
v___x_387_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_386_);
lean_dec_ref(v_env_386_);
v___x_388_ = 512;
v___x_389_ = lean_uint16_land(v___x_384_, v___x_388_);
v___x_390_ = 0;
v___x_391_ = lean_uint16_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
v___y_358_ = v___y_374_;
v___y_359_ = v___y_375_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_380_;
v___y_362_ = v___y_383_;
v___y_363_ = v___x_384_;
v___y_364_ = v___y_373_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___x_387_;
v___y_369_ = v___y_382_;
v___y_370_ = v___y_381_;
v___y_371_ = v___y_378_;
goto v___jp_357_;
}
else
{
v___y_358_ = v___y_374_;
v___y_359_ = v___y_375_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_380_;
v___y_362_ = v___y_383_;
v___y_363_ = v___x_384_;
v___y_364_ = v___y_373_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___x_387_;
v___y_369_ = v___y_382_;
v___y_370_ = v___y_381_;
v___y_371_ = v___y_377_;
goto v___jp_357_;
}
}
v___jp_392_:
{
lean_object* v_toCold_405_; lean_object* v_currRecDepth_406_; lean_object* v_ref_407_; uint8_t v_suppressElabErrors_408_; uint8_t v_isRecordingDeps_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_439_; 
v_toCold_405_ = lean_ctor_get(v___y_403_, 0);
v_currRecDepth_406_ = lean_ctor_get(v___y_403_, 1);
v_ref_407_ = lean_ctor_get(v___y_403_, 2);
v_suppressElabErrors_408_ = lean_ctor_get_uint8(v___y_403_, sizeof(void*)*3 + 2);
v_isRecordingDeps_409_ = lean_ctor_get_uint8(v___y_403_, sizeof(void*)*3 + 3);
v_isSharedCheck_439_ = !lean_is_exclusive(v___y_403_);
if (v_isSharedCheck_439_ == 0)
{
v___x_411_ = v___y_403_;
v_isShared_412_ = v_isSharedCheck_439_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_ref_407_);
lean_inc(v_currRecDepth_406_);
lean_inc(v_toCold_405_);
lean_dec(v___y_403_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_439_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_fileName_413_; lean_object* v_fileMap_414_; lean_object* v_currNamespace_415_; lean_object* v_openDecls_416_; lean_object* v_initHeartbeats_417_; lean_object* v_maxHeartbeats_418_; lean_object* v_quotContext_419_; lean_object* v_currMacroScope_420_; lean_object* v_cancelTk_x3f_421_; lean_object* v_inheritedTraceOptions_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_436_; 
v_fileName_413_ = lean_ctor_get(v_toCold_405_, 0);
v_fileMap_414_ = lean_ctor_get(v_toCold_405_, 1);
v_currNamespace_415_ = lean_ctor_get(v_toCold_405_, 4);
v_openDecls_416_ = lean_ctor_get(v_toCold_405_, 5);
v_initHeartbeats_417_ = lean_ctor_get(v_toCold_405_, 6);
v_maxHeartbeats_418_ = lean_ctor_get(v_toCold_405_, 7);
v_quotContext_419_ = lean_ctor_get(v_toCold_405_, 8);
v_currMacroScope_420_ = lean_ctor_get(v_toCold_405_, 9);
v_cancelTk_x3f_421_ = lean_ctor_get(v_toCold_405_, 10);
v_inheritedTraceOptions_422_ = lean_ctor_get(v_toCold_405_, 11);
v_isSharedCheck_436_ = !lean_is_exclusive(v_toCold_405_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; lean_object* v_unused_438_; 
v_unused_437_ = lean_ctor_get(v_toCold_405_, 3);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_toCold_405_, 2);
lean_dec(v_unused_438_);
v___x_424_ = v_toCold_405_;
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_inheritedTraceOptions_422_);
lean_inc(v_cancelTk_x3f_421_);
lean_inc(v_currMacroScope_420_);
lean_inc(v_quotContext_419_);
lean_inc(v_maxHeartbeats_418_);
lean_inc(v_initHeartbeats_417_);
lean_inc(v_openDecls_416_);
lean_inc(v_currNamespace_415_);
lean_inc(v_fileMap_414_);
lean_inc(v_fileName_413_);
lean_dec(v_toCold_405_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_394_, v___y_402_);
lean_inc_ref(v___y_394_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 3, v___x_426_);
lean_ctor_set(v___x_424_, 2, v___y_394_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_fileName_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_fileMap_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v___y_394_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_currNamespace_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_openDecls_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_initHeartbeats_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_maxHeartbeats_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_quotContext_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_currMacroScope_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_cancelTk_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 11, v_inheritedTraceOptions_422_);
v___x_428_ = v_reuseFailAlloc_435_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_428_);
v___x_430_ = v___x_411_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_currRecDepth_406_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_ref_407_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*3 + 2, v_suppressElabErrors_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*3 + 3, v_isRecordingDeps_409_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_ctor_set_uint16(v___x_430_, sizeof(void*)*3, v___y_397_);
if (v_isRecordingDeps_409_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_432_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_394_, v___x_431_, v___y_398_);
v___y_373_ = v___y_393_;
v___y_374_ = v___x_430_;
v___y_375_ = v___y_395_;
v___y_376_ = v___y_404_;
v___y_377_ = v___y_396_;
v___y_378_ = v___y_398_;
v___y_379_ = v___y_400_;
v___y_380_ = v___y_399_;
v___y_381_ = v___y_402_;
v___y_382_ = v___y_401_;
v___y_383_ = v___x_432_;
goto v___jp_372_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_394_);
v___y_373_ = v___y_393_;
v___y_374_ = v___x_430_;
v___y_375_ = v___y_395_;
v___y_376_ = v___y_404_;
v___y_377_ = v___y_396_;
v___y_378_ = v___y_398_;
v___y_379_ = v___y_400_;
v___y_380_ = v___y_399_;
v___y_381_ = v___y_402_;
v___y_382_ = v___y_401_;
v___y_383_ = v___x_433_;
goto v___jp_372_;
}
}
}
}
}
}
v___jp_440_:
{
lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v_nextMacroScope_456_; lean_object* v_ngen_457_; lean_object* v_auxDeclNGen_458_; lean_object* v_traceState_459_; lean_object* v_recordedDeps_460_; lean_object* v_messages_461_; lean_object* v_infoState_462_; lean_object* v_snapshotTasks_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
v___x_454_ = lean_st_ref_take(v___y_446_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
v_nextMacroScope_456_ = lean_ctor_get(v___x_454_, 1);
v_ngen_457_ = lean_ctor_get(v___x_454_, 2);
v_auxDeclNGen_458_ = lean_ctor_get(v___x_454_, 3);
v_traceState_459_ = lean_ctor_get(v___x_454_, 4);
v_recordedDeps_460_ = lean_ctor_get(v___x_454_, 6);
v_messages_461_ = lean_ctor_get(v___x_454_, 7);
v_infoState_462_ = lean_ctor_get(v___x_454_, 8);
v_snapshotTasks_463_ = lean_ctor_get(v___x_454_, 9);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_454_, 5);
lean_dec(v_unused_473_);
v___x_465_ = v___x_454_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snapshotTasks_463_);
lean_inc(v_infoState_462_);
lean_inc(v_messages_461_);
lean_inc(v_recordedDeps_460_);
lean_inc(v_traceState_459_);
lean_inc(v_auxDeclNGen_458_);
lean_inc(v_ngen_457_);
lean_inc(v_nextMacroScope_456_);
lean_inc(v_env_455_);
lean_dec(v___x_454_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_Kernel_enableDiag(v_env_455_, v___y_447_);
lean_inc_ref(v___y_445_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 5, v___y_445_);
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_nextMacroScope_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_ngen_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_auxDeclNGen_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_traceState_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v___y_445_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_recordedDeps_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_messages_461_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_infoState_462_);
lean_ctor_set(v_reuseFailAlloc_471_, 9, v_snapshotTasks_463_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_st_ref_put(v___y_446_, v___x_469_);
v___y_393_ = v___y_445_;
v___y_394_ = v___y_441_;
v___y_395_ = v___y_442_;
v___y_396_ = v___y_448_;
v___y_397_ = v___y_449_;
v___y_398_ = v___y_450_;
v___y_399_ = v___y_444_;
v___y_400_ = v___y_451_;
v___y_401_ = v___y_453_;
v___y_402_ = v___y_452_;
v___y_403_ = v___y_443_;
v___y_404_ = v___y_446_;
goto v___jp_392_;
}
}
}
v___jp_474_:
{
if (v___y_488_ == 0)
{
if (v___y_487_ == 0)
{
v___y_393_ = v___y_479_;
v___y_394_ = v___y_475_;
v___y_395_ = v___y_476_;
v___y_396_ = v___y_481_;
v___y_397_ = v___y_482_;
v___y_398_ = v___y_483_;
v___y_399_ = v___y_478_;
v___y_400_ = v___y_484_;
v___y_401_ = v___y_486_;
v___y_402_ = v___y_485_;
v___y_403_ = v___y_477_;
v___y_404_ = v___y_480_;
goto v___jp_392_;
}
else
{
v___y_441_ = v___y_475_;
v___y_442_ = v___y_476_;
v___y_443_ = v___y_477_;
v___y_444_ = v___y_478_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_488_;
v___y_448_ = v___y_481_;
v___y_449_ = v___y_482_;
v___y_450_ = v___y_483_;
v___y_451_ = v___y_484_;
v___y_452_ = v___y_485_;
v___y_453_ = v___y_486_;
goto v___jp_440_;
}
}
else
{
if (v___y_487_ == 0)
{
v___y_441_ = v___y_475_;
v___y_442_ = v___y_476_;
v___y_443_ = v___y_477_;
v___y_444_ = v___y_478_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_488_;
v___y_448_ = v___y_481_;
v___y_449_ = v___y_482_;
v___y_450_ = v___y_483_;
v___y_451_ = v___y_484_;
v___y_452_ = v___y_485_;
v___y_453_ = v___y_486_;
goto v___jp_440_;
}
else
{
v___y_393_ = v___y_479_;
v___y_394_ = v___y_475_;
v___y_395_ = v___y_476_;
v___y_396_ = v___y_481_;
v___y_397_ = v___y_482_;
v___y_398_ = v___y_483_;
v___y_399_ = v___y_478_;
v___y_400_ = v___y_484_;
v___y_401_ = v___y_486_;
v___y_402_ = v___y_485_;
v___y_403_ = v___y_477_;
v___y_404_ = v___y_480_;
goto v___jp_392_;
}
}
}
v___jp_489_:
{
uint16_t v___x_501_; lean_object* v___x_502_; lean_object* v_env_503_; uint8_t v___x_504_; uint16_t v___x_505_; uint16_t v___x_506_; uint16_t v___x_507_; uint8_t v___x_508_; 
v___x_501_ = l_Lean_OptionFlags_ofOptions(v___y_500_);
v___x_502_ = lean_st_ref_get(v___y_493_);
v_env_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc_ref(v_env_503_);
lean_dec(v___x_502_);
v___x_504_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_503_);
lean_dec_ref(v_env_503_);
v___x_505_ = 512;
v___x_506_ = lean_uint16_land(v___x_501_, v___x_505_);
v___x_507_ = 0;
v___x_508_ = lean_uint16_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
v___y_475_ = v___y_500_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v___y_497_;
v___y_479_ = v___y_490_;
v___y_480_ = v___y_493_;
v___y_481_ = v___y_494_;
v___y_482_ = v___x_501_;
v___y_483_ = v___y_495_;
v___y_484_ = v___y_496_;
v___y_485_ = v___y_498_;
v___y_486_ = v___y_499_;
v___y_487_ = v___x_504_;
v___y_488_ = v___y_495_;
goto v___jp_474_;
}
else
{
v___y_475_ = v___y_500_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v___y_497_;
v___y_479_ = v___y_490_;
v___y_480_ = v___y_493_;
v___y_481_ = v___y_494_;
v___y_482_ = v___x_501_;
v___y_483_ = v___y_495_;
v___y_484_ = v___y_496_;
v___y_485_ = v___y_498_;
v___y_486_ = v___y_499_;
v___y_487_ = v___x_504_;
v___y_488_ = v___y_494_;
goto v___jp_474_;
}
}
v___jp_509_:
{
lean_object* v_toCold_521_; lean_object* v_currRecDepth_522_; lean_object* v_ref_523_; uint8_t v_suppressElabErrors_524_; uint8_t v_isRecordingDeps_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_556_; 
v_toCold_521_ = lean_ctor_get(v___y_519_, 0);
v_currRecDepth_522_ = lean_ctor_get(v___y_519_, 1);
v_ref_523_ = lean_ctor_get(v___y_519_, 2);
v_suppressElabErrors_524_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 2);
v_isRecordingDeps_525_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 3);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_519_);
if (v_isSharedCheck_556_ == 0)
{
v___x_527_ = v___y_519_;
v_isShared_528_ = v_isSharedCheck_556_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_ref_523_);
lean_inc(v_currRecDepth_522_);
lean_inc(v_toCold_521_);
lean_dec(v___y_519_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_556_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_fileName_529_; lean_object* v_fileMap_530_; lean_object* v_currNamespace_531_; lean_object* v_openDecls_532_; lean_object* v_initHeartbeats_533_; lean_object* v_maxHeartbeats_534_; lean_object* v_quotContext_535_; lean_object* v_currMacroScope_536_; lean_object* v_cancelTk_x3f_537_; lean_object* v_inheritedTraceOptions_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_553_; 
v_fileName_529_ = lean_ctor_get(v_toCold_521_, 0);
v_fileMap_530_ = lean_ctor_get(v_toCold_521_, 1);
v_currNamespace_531_ = lean_ctor_get(v_toCold_521_, 4);
v_openDecls_532_ = lean_ctor_get(v_toCold_521_, 5);
v_initHeartbeats_533_ = lean_ctor_get(v_toCold_521_, 6);
v_maxHeartbeats_534_ = lean_ctor_get(v_toCold_521_, 7);
v_quotContext_535_ = lean_ctor_get(v_toCold_521_, 8);
v_currMacroScope_536_ = lean_ctor_get(v_toCold_521_, 9);
v_cancelTk_x3f_537_ = lean_ctor_get(v_toCold_521_, 10);
v_inheritedTraceOptions_538_ = lean_ctor_get(v_toCold_521_, 11);
v_isSharedCheck_553_ = !lean_is_exclusive(v_toCold_521_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; 
v_unused_554_ = lean_ctor_get(v_toCold_521_, 3);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_toCold_521_, 2);
lean_dec(v_unused_555_);
v___x_540_ = v_toCold_521_;
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_inheritedTraceOptions_538_);
lean_inc(v_cancelTk_x3f_537_);
lean_inc(v_currMacroScope_536_);
lean_inc(v_quotContext_535_);
lean_inc(v_maxHeartbeats_534_);
lean_inc(v_initHeartbeats_533_);
lean_inc(v_openDecls_532_);
lean_inc(v_currNamespace_531_);
lean_inc(v_fileMap_530_);
lean_inc(v_fileName_529_);
lean_dec(v_toCold_521_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = l_Lean_maxRecDepth;
v___x_543_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_511_, v___x_542_);
lean_inc_ref(v___y_511_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 3, v___x_543_);
lean_ctor_set(v___x_540_, 2, v___y_511_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fileName_529_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_fileMap_530_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___y_511_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_currNamespace_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v_openDecls_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 6, v_initHeartbeats_533_);
lean_ctor_set(v_reuseFailAlloc_552_, 7, v_maxHeartbeats_534_);
lean_ctor_set(v_reuseFailAlloc_552_, 8, v_quotContext_535_);
lean_ctor_set(v_reuseFailAlloc_552_, 9, v_currMacroScope_536_);
lean_ctor_set(v_reuseFailAlloc_552_, 10, v_cancelTk_x3f_537_);
lean_ctor_set(v_reuseFailAlloc_552_, 11, v_inheritedTraceOptions_538_);
v___x_545_ = v_reuseFailAlloc_552_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_545_);
v___x_547_ = v___x_527_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_currRecDepth_522_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ref_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*3 + 2, v_suppressElabErrors_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*3 + 3, v_isRecordingDeps_525_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_ctor_set_uint16(v___x_547_, sizeof(void*)*3, v___y_513_);
if (v_isRecordingDeps_525_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_549_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_511_, v___x_548_, v_isRecordingDeps_525_);
v___y_490_ = v___y_510_;
v___y_491_ = v___y_512_;
v___y_492_ = v___x_547_;
v___y_493_ = v___y_520_;
v___y_494_ = v___y_514_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_517_;
v___y_497_ = v___y_516_;
v___y_498_ = v___x_542_;
v___y_499_ = v___y_518_;
v___y_500_ = v___x_549_;
goto v___jp_489_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_511_);
v___y_490_ = v___y_510_;
v___y_491_ = v___y_512_;
v___y_492_ = v___x_547_;
v___y_493_ = v___y_520_;
v___y_494_ = v___y_514_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_517_;
v___y_497_ = v___y_516_;
v___y_498_ = v___x_542_;
v___y_499_ = v___y_518_;
v___y_500_ = v___x_550_;
goto v___jp_489_;
}
}
}
}
}
}
v___jp_557_:
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v_nextMacroScope_572_; lean_object* v_ngen_573_; lean_object* v_auxDeclNGen_574_; lean_object* v_traceState_575_; lean_object* v_recordedDeps_576_; lean_object* v_messages_577_; lean_object* v_infoState_578_; lean_object* v_snapshotTasks_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_588_; 
v___x_570_ = lean_st_ref_take(v___y_565_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
v_nextMacroScope_572_ = lean_ctor_get(v___x_570_, 1);
v_ngen_573_ = lean_ctor_get(v___x_570_, 2);
v_auxDeclNGen_574_ = lean_ctor_get(v___x_570_, 3);
v_traceState_575_ = lean_ctor_get(v___x_570_, 4);
v_recordedDeps_576_ = lean_ctor_get(v___x_570_, 6);
v_messages_577_ = lean_ctor_get(v___x_570_, 7);
v_infoState_578_ = lean_ctor_get(v___x_570_, 8);
v_snapshotTasks_579_ = lean_ctor_get(v___x_570_, 9);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v___x_570_, 5);
lean_dec(v_unused_589_);
v___x_581_ = v___x_570_;
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snapshotTasks_579_);
lean_inc(v_infoState_578_);
lean_inc(v_messages_577_);
lean_inc(v_recordedDeps_576_);
lean_inc(v_traceState_575_);
lean_inc(v_auxDeclNGen_574_);
lean_inc(v_ngen_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_env_571_);
lean_dec(v___x_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = l_Lean_Kernel_enableDiag(v_env_571_, v___y_566_);
lean_inc_ref(v___y_562_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 5, v___y_562_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_ngen_573_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_auxDeclNGen_574_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_traceState_575_);
lean_ctor_set(v_reuseFailAlloc_587_, 5, v___y_562_);
lean_ctor_set(v_reuseFailAlloc_587_, 6, v_recordedDeps_576_);
lean_ctor_set(v_reuseFailAlloc_587_, 7, v_messages_577_);
lean_ctor_set(v_reuseFailAlloc_587_, 8, v_infoState_578_);
lean_ctor_set(v_reuseFailAlloc_587_, 9, v_snapshotTasks_579_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_st_ref_put(v___y_565_, v___x_585_);
v___y_510_ = v___y_562_;
v___y_511_ = v___y_558_;
v___y_512_ = v___y_559_;
v___y_513_ = v___y_563_;
v___y_514_ = v___y_564_;
v___y_515_ = v___y_567_;
v___y_516_ = v___y_561_;
v___y_517_ = v___y_568_;
v___y_518_ = v___y_569_;
v___y_519_ = v___y_560_;
v___y_520_ = v___y_565_;
goto v___jp_509_;
}
}
}
v___jp_590_:
{
if (v___y_603_ == 0)
{
if (v___y_596_ == 0)
{
v___y_510_ = v___y_595_;
v___y_511_ = v___y_591_;
v___y_512_ = v___y_592_;
v___y_513_ = v___y_597_;
v___y_514_ = v___y_598_;
v___y_515_ = v___y_600_;
v___y_516_ = v___y_594_;
v___y_517_ = v___y_601_;
v___y_518_ = v___y_602_;
v___y_519_ = v___y_593_;
v___y_520_ = v___y_599_;
goto v___jp_509_;
}
else
{
v___y_558_ = v___y_591_;
v___y_559_ = v___y_592_;
v___y_560_ = v___y_593_;
v___y_561_ = v___y_594_;
v___y_562_ = v___y_595_;
v___y_563_ = v___y_597_;
v___y_564_ = v___y_598_;
v___y_565_ = v___y_599_;
v___y_566_ = v___y_603_;
v___y_567_ = v___y_600_;
v___y_568_ = v___y_601_;
v___y_569_ = v___y_602_;
goto v___jp_557_;
}
}
else
{
if (v___y_596_ == 0)
{
v___y_558_ = v___y_591_;
v___y_559_ = v___y_592_;
v___y_560_ = v___y_593_;
v___y_561_ = v___y_594_;
v___y_562_ = v___y_595_;
v___y_563_ = v___y_597_;
v___y_564_ = v___y_598_;
v___y_565_ = v___y_599_;
v___y_566_ = v___y_603_;
v___y_567_ = v___y_600_;
v___y_568_ = v___y_601_;
v___y_569_ = v___y_602_;
goto v___jp_557_;
}
else
{
v___y_510_ = v___y_595_;
v___y_511_ = v___y_591_;
v___y_512_ = v___y_592_;
v___y_513_ = v___y_597_;
v___y_514_ = v___y_598_;
v___y_515_ = v___y_600_;
v___y_516_ = v___y_594_;
v___y_517_ = v___y_601_;
v___y_518_ = v___y_602_;
v___y_519_ = v___y_593_;
v___y_520_ = v___y_599_;
goto v___jp_509_;
}
}
}
v___jp_604_:
{
uint16_t v___x_615_; lean_object* v___x_616_; lean_object* v_env_617_; uint8_t v___x_618_; uint16_t v___x_619_; uint16_t v___x_620_; uint16_t v___x_621_; uint8_t v___x_622_; 
v___x_615_ = l_Lean_OptionFlags_ofOptions(v___y_614_);
v___x_616_ = lean_st_ref_get(v___y_609_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
v___x_618_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_617_);
lean_dec_ref(v_env_617_);
v___x_619_ = 512;
v___x_620_ = lean_uint16_land(v___x_615_, v___x_619_);
v___x_621_ = 0;
v___x_622_ = lean_uint16_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
v___y_591_ = v___y_614_;
v___y_592_ = v___y_606_;
v___y_593_ = v___y_607_;
v___y_594_ = v___y_612_;
v___y_595_ = v___y_605_;
v___y_596_ = v___x_618_;
v___y_597_ = v___x_615_;
v___y_598_ = v___y_608_;
v___y_599_ = v___y_609_;
v___y_600_ = v___y_610_;
v___y_601_ = v___y_611_;
v___y_602_ = v___y_613_;
v___y_603_ = v___y_610_;
goto v___jp_590_;
}
else
{
v___y_591_ = v___y_614_;
v___y_592_ = v___y_606_;
v___y_593_ = v___y_607_;
v___y_594_ = v___y_612_;
v___y_595_ = v___y_605_;
v___y_596_ = v___x_618_;
v___y_597_ = v___x_615_;
v___y_598_ = v___y_608_;
v___y_599_ = v___y_609_;
v___y_600_ = v___y_610_;
v___y_601_ = v___y_611_;
v___y_602_ = v___y_613_;
v___y_603_ = v___y_608_;
goto v___jp_590_;
}
}
v___jp_623_:
{
lean_object* v___x_632_; 
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc_ref(v___y_625_);
v___x_632_ = lean_infer_type(v___y_625_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_n(v_a_633_, 2);
lean_dec_ref_known(v___x_632_, 1);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
v___x_634_ = lean_apply_6(v_checkType_261_, v_a_633_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, lean_box(0));
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_env_642_; lean_object* v_nextMacroScope_643_; lean_object* v_ngen_644_; lean_object* v_auxDeclNGen_645_; lean_object* v_traceState_646_; lean_object* v_recordedDeps_647_; lean_object* v_messages_648_; lean_object* v_infoState_649_; lean_object* v_snapshotTasks_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref_known(v___x_634_, 1);
v___x_635_ = lean_array_to_list(v___y_627_);
lean_inc_n(v___y_624_, 2);
v___x_636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_636_, 0, v___y_624_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_ctor_set(v___x_636_, 2, v_a_633_);
v___x_637_ = lean_box(0);
lean_inc(v___y_626_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___y_624_);
lean_ctor_set(v___x_638_, 1, v___y_626_);
v___x_639_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_639_, 0, v___x_636_);
lean_ctor_set(v___x_639_, 1, v___y_625_);
lean_ctor_set(v___x_639_, 2, v___x_637_);
lean_ctor_set(v___x_639_, 3, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*4, v_safety_262_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = lean_st_ref_take(v___y_631_);
v_env_642_ = lean_ctor_get(v___x_641_, 0);
v_nextMacroScope_643_ = lean_ctor_get(v___x_641_, 1);
v_ngen_644_ = lean_ctor_get(v___x_641_, 2);
v_auxDeclNGen_645_ = lean_ctor_get(v___x_641_, 3);
v_traceState_646_ = lean_ctor_get(v___x_641_, 4);
v_recordedDeps_647_ = lean_ctor_get(v___x_641_, 6);
v_messages_648_ = lean_ctor_get(v___x_641_, 7);
v_infoState_649_ = lean_ctor_get(v___x_641_, 8);
v_snapshotTasks_650_ = lean_ctor_get(v___x_641_, 9);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_641_, 5);
lean_dec(v_unused_697_);
v___x_652_ = v___x_641_;
v_isShared_653_ = v_isSharedCheck_696_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snapshotTasks_650_);
lean_inc(v_infoState_649_);
lean_inc(v_messages_648_);
lean_inc(v_recordedDeps_647_);
lean_inc(v_traceState_646_);
lean_inc(v_auxDeclNGen_645_);
lean_inc(v_ngen_644_);
lean_inc(v_nextMacroScope_643_);
lean_inc(v_env_642_);
lean_dec(v___x_641_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_696_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_inc(v___y_624_);
v___x_654_ = l_Lean_markMeta(v_env_642_, v___y_624_);
v___x_655_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 5, v___x_655_);
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_nextMacroScope_643_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_ngen_644_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_auxDeclNGen_645_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_traceState_646_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_recordedDeps_647_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_messages_648_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_infoState_649_);
lean_ctor_set(v_reuseFailAlloc_695_, 9, v_snapshotTasks_650_);
v___x_657_ = v_reuseFailAlloc_695_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_mctx_660_; lean_object* v_zetaDeltaFVarIds_661_; lean_object* v_postponed_662_; lean_object* v_diag_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_693_; 
v___x_658_ = lean_st_ref_put(v___y_631_, v___x_657_);
v___x_659_ = lean_st_ref_take(v___y_629_);
v_mctx_660_ = lean_ctor_get(v___x_659_, 0);
v_zetaDeltaFVarIds_661_ = lean_ctor_get(v___x_659_, 2);
v_postponed_662_ = lean_ctor_get(v___x_659_, 3);
v_diag_663_ = lean_ctor_get(v___x_659_, 4);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_659_, 1);
lean_dec(v_unused_694_);
v___x_665_ = v___x_659_;
v_isShared_666_ = v_isSharedCheck_693_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_diag_663_);
lean_inc(v_postponed_662_);
lean_inc(v_zetaDeltaFVarIds_661_);
lean_inc(v_mctx_660_);
lean_dec(v___x_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_693_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_mctx_660_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_zetaDeltaFVarIds_661_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_postponed_662_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_diag_663_);
v___x_669_ = v_reuseFailAlloc_692_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_env_672_; lean_object* v_checked_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = lean_st_ref_put(v___y_629_, v___x_669_);
v___x_671_ = lean_st_ref_get(v___y_631_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_env_672_);
lean_dec(v___x_671_);
v_checked_673_ = lean_ctor_get(v_env_672_, 2);
lean_inc_ref(v_checked_673_);
lean_dec_ref(v_env_672_);
v___x_674_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_675_ = l_Lean_traceBlock___redArg(v___x_674_, v_checked_673_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_toCold_676_; uint8_t v_isRecordingDeps_677_; lean_object* v_options_678_; uint8_t v___x_679_; uint8_t v___x_680_; 
lean_dec_ref_known(v___x_675_, 1);
v_toCold_676_ = lean_ctor_get(v___y_630_, 0);
v_isRecordingDeps_677_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*3 + 3);
v_options_678_ = lean_ctor_get(v_toCold_676_, 2);
v___x_679_ = 1;
v___x_680_ = 0;
if (v_isRecordingDeps_677_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lean_Elab_async;
lean_inc_ref(v_options_678_);
v___x_682_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_options_678_, v___x_681_, v_isRecordingDeps_677_);
v___y_605_ = v___x_655_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_630_;
v___y_608_ = v___x_680_;
v___y_609_ = v___y_631_;
v___y_610_ = v___x_679_;
v___y_611_ = v___x_640_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v___x_682_;
goto v___jp_604_;
}
else
{
lean_object* v___x_683_; 
lean_inc_ref(v_options_678_);
v___x_683_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_678_);
v___y_605_ = v___x_655_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_630_;
v___y_608_ = v___x_680_;
v___y_609_ = v___y_631_;
v___y_610_ = v___x_679_;
v___y_611_ = v___x_640_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v___x_683_;
goto v___jp_604_;
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref_known(v___x_640_, 1);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_624_);
v_a_684_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_675_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
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
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_a_633_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
v_a_698_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_634_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_634_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v_checkType_261_);
v_a_706_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_632_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_632_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
v___jp_714_:
{
lean_object* v___x_715_; lean_object* v_env_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_715_ = lean_st_ref_get(v___y_267_);
v_env_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_ref(v_env_716_);
lean_dec(v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_718_ = l_Lean_Core_mkFreshUserName(v___x_717_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_mkPrivateName(v_env_716_, v_a_719_);
lean_dec_ref(v_env_716_);
v___x_721_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_263_, v___y_265_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_params_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_n(v_a_722_, 2);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_724_ = l_Lean_collectLevelParams(v___x_723_, v_a_722_);
v_params_725_ = lean_ctor_get(v___x_724_, 2);
lean_inc_ref(v_params_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = lean_box(0);
v___x_727_ = l_Lean_Expr_hasMVar(v_a_722_);
if (v___x_727_ == 0)
{
v___y_624_ = v___x_720_;
v___y_625_ = v_a_722_;
v___y_626_ = v___x_726_;
v___y_627_ = v_params_725_;
v___y_628_ = v___y_264_;
v___y_629_ = v___y_265_;
v___y_630_ = v___y_266_;
v___y_631_ = v___y_267_;
goto v___jp_623_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_722_);
v___x_729_ = l_Lean_indentExpr(v_a_722_);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_730_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
v___y_624_ = v___x_720_;
v___y_625_ = v_a_722_;
v___y_626_ = v___x_726_;
v___y_627_ = v_params_725_;
v___y_628_ = v___y_264_;
v___y_629_ = v___y_265_;
v___y_630_ = v___y_266_;
v___y_631_ = v___y_267_;
goto v___jp_623_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_params_725_);
lean_dec(v_a_722_);
lean_dec(v___x_720_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_checkType_261_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___x_720_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_checkType_261_);
v_a_740_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_721_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_721_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_env_716_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_value_263_);
lean_dec_ref(v_checkType_261_);
v_a_748_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_718_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_718_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
v___jp_756_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_mctx_770_; lean_object* v_zetaDeltaFVarIds_771_; lean_object* v_postponed_772_; lean_object* v_diag_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v___x_766_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_767_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_767_, 0, v___y_765_);
lean_ctor_set(v___x_767_, 1, v_nextMacroScope_757_);
lean_ctor_set(v___x_767_, 2, v_ngen_758_);
lean_ctor_set(v___x_767_, 3, v_auxDeclNGen_759_);
lean_ctor_set(v___x_767_, 4, v_traceState_760_);
lean_ctor_set(v___x_767_, 5, v___x_766_);
lean_ctor_set(v___x_767_, 6, v_recordedDeps_761_);
lean_ctor_set(v___x_767_, 7, v_messages_762_);
lean_ctor_set(v___x_767_, 8, v_infoState_763_);
lean_ctor_set(v___x_767_, 9, v_snapshotTasks_764_);
v___x_768_ = lean_st_ref_put(v___y_267_, v___x_767_);
v___x_769_ = lean_st_ref_take(v___y_265_);
v_mctx_770_ = lean_ctor_get(v___x_769_, 0);
v_zetaDeltaFVarIds_771_ = lean_ctor_get(v___x_769_, 2);
v_postponed_772_ = lean_ctor_get(v___x_769_, 3);
v_diag_773_ = lean_ctor_get(v___x_769_, 4);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_769_, 1);
lean_dec(v_unused_783_);
v___x_775_ = v___x_769_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_diag_773_);
lean_inc(v_postponed_772_);
lean_inc(v_zetaDeltaFVarIds_771_);
lean_inc(v_mctx_770_);
lean_dec(v___x_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_mctx_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_zetaDeltaFVarIds_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_postponed_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_diag_773_);
v___x_779_ = v_reuseFailAlloc_781_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; 
v___x_780_ = lean_st_ref_put(v___y_265_, v___x_779_);
goto v___jp_714_;
}
}
}
v___jp_785_:
{
lean_object* v___x_786_; lean_object* v_env_787_; lean_object* v_nextMacroScope_788_; lean_object* v_ngen_789_; lean_object* v_auxDeclNGen_790_; lean_object* v_traceState_791_; lean_object* v_recordedDeps_792_; lean_object* v_messages_793_; lean_object* v_infoState_794_; lean_object* v_snapshotTasks_795_; lean_object* v___x_796_; 
v___x_786_ = lean_st_ref_take(v___y_267_);
v_env_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref_n(v_env_787_, 2);
v_nextMacroScope_788_ = lean_ctor_get(v___x_786_, 1);
lean_inc(v_nextMacroScope_788_);
v_ngen_789_ = lean_ctor_get(v___x_786_, 2);
lean_inc_ref(v_ngen_789_);
v_auxDeclNGen_790_ = lean_ctor_get(v___x_786_, 3);
lean_inc_ref(v_auxDeclNGen_790_);
v_traceState_791_ = lean_ctor_get(v___x_786_, 4);
lean_inc_ref(v_traceState_791_);
v_recordedDeps_792_ = lean_ctor_get(v___x_786_, 6);
lean_inc_ref(v_recordedDeps_792_);
v_messages_793_ = lean_ctor_get(v___x_786_, 7);
lean_inc_ref(v_messages_793_);
v_infoState_794_ = lean_ctor_get(v___x_786_, 8);
lean_inc_ref(v_infoState_794_);
v_snapshotTasks_795_ = lean_ctor_get(v___x_786_, 9);
lean_inc_ref(v_snapshotTasks_795_);
lean_dec(v___x_786_);
v___x_796_ = l_Lean_Environment_importEnv_x3f(v_env_787_);
if (lean_obj_tag(v___x_796_) == 0)
{
v_nextMacroScope_757_ = v_nextMacroScope_788_;
v_ngen_758_ = v_ngen_789_;
v_auxDeclNGen_759_ = v_auxDeclNGen_790_;
v_traceState_760_ = v_traceState_791_;
v_recordedDeps_761_ = v_recordedDeps_792_;
v_messages_762_ = v_messages_793_;
v_infoState_763_ = v_infoState_794_;
v_snapshotTasks_764_ = v_snapshotTasks_795_;
v___y_765_ = v_env_787_;
goto v___jp_756_;
}
else
{
lean_object* v_val_797_; 
lean_dec_ref(v_env_787_);
v_val_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_796_, 1);
v_nextMacroScope_757_ = v_nextMacroScope_788_;
v_ngen_758_ = v_ngen_789_;
v_auxDeclNGen_759_ = v_auxDeclNGen_790_;
v_traceState_760_ = v_traceState_791_;
v_recordedDeps_761_ = v_recordedDeps_792_;
v_messages_762_ = v_messages_793_;
v_infoState_763_ = v_infoState_794_;
v_snapshotTasks_764_ = v_snapshotTasks_795_;
v___y_765_ = v_val_797_;
goto v___jp_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_806_, lean_object* v_checkType_807_, lean_object* v_safety_808_, lean_object* v_value_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_checkMeta_boxed_815_; uint8_t v_safety_boxed_816_; lean_object* v_res_817_; 
v_checkMeta_boxed_815_ = lean_unbox(v_checkMeta_806_);
v_safety_boxed_816_ = lean_unbox(v_safety_808_);
v_res_817_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_815_, v_checkType_807_, v_safety_boxed_816_, v_value_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object* v_env_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_nextMacroScope_823_; lean_object* v_ngen_824_; lean_object* v_auxDeclNGen_825_; lean_object* v_traceState_826_; lean_object* v_recordedDeps_827_; lean_object* v_messages_828_; lean_object* v_infoState_829_; lean_object* v_snapshotTasks_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_856_; 
v___x_822_ = lean_st_ref_take(v___y_820_);
v_nextMacroScope_823_ = lean_ctor_get(v___x_822_, 1);
v_ngen_824_ = lean_ctor_get(v___x_822_, 2);
v_auxDeclNGen_825_ = lean_ctor_get(v___x_822_, 3);
v_traceState_826_ = lean_ctor_get(v___x_822_, 4);
v_recordedDeps_827_ = lean_ctor_get(v___x_822_, 6);
v_messages_828_ = lean_ctor_get(v___x_822_, 7);
v_infoState_829_ = lean_ctor_get(v___x_822_, 8);
v_snapshotTasks_830_ = lean_ctor_get(v___x_822_, 9);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_857_ = lean_ctor_get(v___x_822_, 5);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_858_);
v___x_832_ = v___x_822_;
v_isShared_833_ = v_isSharedCheck_856_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snapshotTasks_830_);
lean_inc(v_infoState_829_);
lean_inc(v_messages_828_);
lean_inc(v_recordedDeps_827_);
lean_inc(v_traceState_826_);
lean_inc(v_auxDeclNGen_825_);
lean_inc(v_ngen_824_);
lean_inc(v_nextMacroScope_823_);
lean_dec(v___x_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_856_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 5, v___x_834_);
lean_ctor_set(v___x_832_, 0, v_env_818_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_env_818_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_nextMacroScope_823_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_ngen_824_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_auxDeclNGen_825_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_traceState_826_);
lean_ctor_set(v_reuseFailAlloc_855_, 5, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_855_, 6, v_recordedDeps_827_);
lean_ctor_set(v_reuseFailAlloc_855_, 7, v_messages_828_);
lean_ctor_set(v_reuseFailAlloc_855_, 8, v_infoState_829_);
lean_ctor_set(v_reuseFailAlloc_855_, 9, v_snapshotTasks_830_);
v___x_836_ = v_reuseFailAlloc_855_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_mctx_839_; lean_object* v_zetaDeltaFVarIds_840_; lean_object* v_postponed_841_; lean_object* v_diag_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_853_; 
v___x_837_ = lean_st_ref_put(v___y_820_, v___x_836_);
v___x_838_ = lean_st_ref_take(v___y_819_);
v_mctx_839_ = lean_ctor_get(v___x_838_, 0);
v_zetaDeltaFVarIds_840_ = lean_ctor_get(v___x_838_, 2);
v_postponed_841_ = lean_ctor_get(v___x_838_, 3);
v_diag_842_ = lean_ctor_get(v___x_838_, 4);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_838_, 1);
lean_dec(v_unused_854_);
v___x_844_ = v___x_838_;
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_diag_842_);
lean_inc(v_postponed_841_);
lean_inc(v_zetaDeltaFVarIds_840_);
lean_inc(v_mctx_839_);
lean_dec(v___x_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_box(0);
v___x_847_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_mctx_839_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_zetaDeltaFVarIds_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_postponed_841_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_diag_842_);
v___x_849_ = v_reuseFailAlloc_852_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_st_ref_put(v___y_819_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_846_);
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object* v_env_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object* v_env_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; lean_object* v_env_872_; lean_object* v_a_874_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_871_ = lean_st_ref_get(v___y_869_);
v_env_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc_ref(v_env_872_);
lean_dec(v___x_871_);
v___x_884_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_864_, v___y_867_, v___y_869_);
lean_dec_ref(v___x_884_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
v___x_885_ = lean_apply_5(v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, lean_box(0));
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_872_, v___y_867_, v___y_869_);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_895_);
v___x_889_ = v___x_887_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_dec(v___x_887_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_a_886_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_886_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v_a_896_; 
v_a_896_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_885_, 1);
v_a_874_ = v_a_896_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v___x_875_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_872_, v___y_867_, v___y_869_);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_875_, 0);
lean_dec(v_unused_883_);
v___x_877_ = v___x_875_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_875_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 1);
lean_ctor_set(v___x_877_, 0, v_a_874_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_874_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object* v_env_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_897_, v_x_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_905_, lean_object* v_checkType_906_, uint8_t v_safety_907_, uint8_t v_checkMeta_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_914_ = lean_box(v_checkMeta_908_);
v___x_915_ = lean_box(v_safety_907_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_916_, 0, v___x_914_);
lean_closure_set(v___f_916_, 1, v_checkType_906_);
lean_closure_set(v___f_916_, 2, v___x_915_);
lean_closure_set(v___f_916_, 3, v_value_905_);
v___x_917_ = lean_st_ref_get(v_a_912_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_919_ = l_Lean_Environment_unlockAsync(v_env_918_);
v___x_920_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v___x_919_, v___f_916_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_921_, lean_object* v_checkType_922_, lean_object* v_safety_923_, lean_object* v_checkMeta_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
uint8_t v_safety_boxed_930_; uint8_t v_checkMeta_boxed_931_; lean_object* v_res_932_; 
v_safety_boxed_930_ = lean_unbox(v_safety_923_);
v_checkMeta_boxed_931_ = lean_unbox(v_checkMeta_924_);
v_res_932_ = l_Lean_Meta_evalExprCore___redArg(v_value_921_, v_checkType_922_, v_safety_boxed_930_, v_checkMeta_boxed_931_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_933_, lean_object* v_value_934_, lean_object* v_checkType_935_, uint8_t v_safety_936_, uint8_t v_checkMeta_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_evalExprCore___redArg(v_value_934_, v_checkType_935_, v_safety_936_, v_checkMeta_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_944_, lean_object* v_value_945_, lean_object* v_checkType_946_, lean_object* v_safety_947_, lean_object* v_checkMeta_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_safety_boxed_954_; uint8_t v_checkMeta_boxed_955_; lean_object* v_res_956_; 
v_safety_boxed_954_ = lean_unbox(v_safety_947_);
v_checkMeta_boxed_955_ = lean_unbox(v_checkMeta_948_);
v_res_956_ = l_Lean_Meta_evalExprCore(v_00_u03b1_944_, v_value_945_, v_checkType_946_, v_safety_boxed_954_, v_checkMeta_boxed_955_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_object* v_00_u03b1_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___boxed(lean_object* v_00_u03b1_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(v_00_u03b1_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_00_u03b1_971_, lean_object* v_constName_972_, uint8_t v_checkMeta_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_972_, v_checkMeta_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_00_u03b1_980_, lean_object* v_constName_981_, lean_object* v_checkMeta_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_checkMeta_boxed_988_; lean_object* v_res_989_; 
v_checkMeta_boxed_988_ = lean_unbox(v_checkMeta_982_);
v_res_989_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(v_00_u03b1_980_, v_constName_981_, v_checkMeta_boxed_988_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_998_, lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_998_, v_msg_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object* v_env_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_1006_, v___y_1008_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object* v_env_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v_00_u03b1_1020_, lean_object* v_env_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_1021_, v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_env_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(v_00_u03b1_1029_, v_env_1030_, v_x_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_object* v_00_u03b1_1038_, lean_object* v_x_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(v_00_u03b1_1046_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1057_, lean_object* v_type_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_whnfD(v_type_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1078_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1078_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1078_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Expr_isConstOf(v_a_1065_, v_typeName_1057_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1067_);
v___x_1070_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1071_ = l_Lean_indentExpr(v_a_1065_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1072_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec(v_a_1065_);
v___x_1074_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1074_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
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
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1064_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1064_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1087_, lean_object* v_type_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1087_, v_type_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v_typeName_1087_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1095_, lean_object* v_value_1096_, uint8_t v_safety_1097_, uint8_t v_checkMeta_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1104_, 0, v_typeName_1095_);
v___x_1105_ = l_Lean_Meta_evalExprCore___redArg(v_value_1096_, v___f_1104_, v_safety_1097_, v_checkMeta_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1106_, lean_object* v_value_1107_, lean_object* v_safety_1108_, lean_object* v_checkMeta_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_safety_boxed_1115_; uint8_t v_checkMeta_boxed_1116_; lean_object* v_res_1117_; 
v_safety_boxed_1115_ = lean_unbox(v_safety_1108_);
v_checkMeta_boxed_1116_ = lean_unbox(v_checkMeta_1109_);
v_res_1117_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1106_, v_value_1107_, v_safety_boxed_1115_, v_checkMeta_boxed_1116_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1118_, lean_object* v_typeName_1119_, lean_object* v_value_1120_, uint8_t v_safety_1121_, uint8_t v_checkMeta_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1119_, v_value_1120_, v_safety_1121_, v_checkMeta_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_typeName_1130_, lean_object* v_value_1131_, lean_object* v_safety_1132_, lean_object* v_checkMeta_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_safety_boxed_1139_; uint8_t v_checkMeta_boxed_1140_; lean_object* v_res_1141_; 
v_safety_boxed_1139_ = lean_unbox(v_safety_1132_);
v_checkMeta_boxed_1140_ = lean_unbox(v_checkMeta_1133_);
v_res_1141_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1129_, v_typeName_1130_, v_value_1131_, v_safety_boxed_1139_, v_checkMeta_boxed_1140_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1147_, lean_object* v_type_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
lean_inc_ref(v_expectedType_1147_);
lean_inc_ref(v_type_1148_);
v___x_1154_ = l_Lean_Meta_isExprDefEq(v_type_1148_, v_expectedType_1147_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1179_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1179_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1179_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_unbox(v_a_1155_);
lean_dec(v_a_1155_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1157_);
v___x_1160_ = lean_box(0);
v___x_1161_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1162_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1148_, v_expectedType_1147_, v___x_1160_, v___x_1161_, v___y_1149_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_a_1163_);
v___x_1166_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1165_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1166_;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1162_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
lean_dec_ref(v_type_1148_);
lean_dec_ref(v_expectedType_1147_);
v___x_1175_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1175_);
v___x_1177_ = v___x_1157_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_type_1148_);
lean_dec_ref(v_expectedType_1147_);
v_a_1180_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1154_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1154_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1188_, lean_object* v_type_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1188_, v_type_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1196_, lean_object* v_value_1197_, uint8_t v_safety_1198_, uint8_t v_checkMeta_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___f_1205_; lean_object* v___x_1206_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1205_, 0, v_expectedType_1196_);
v___x_1206_ = l_Lean_Meta_evalExprCore___redArg(v_value_1197_, v___f_1205_, v_safety_1198_, v_checkMeta_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1207_, lean_object* v_value_1208_, lean_object* v_safety_1209_, lean_object* v_checkMeta_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
uint8_t v_safety_boxed_1216_; uint8_t v_checkMeta_boxed_1217_; lean_object* v_res_1218_; 
v_safety_boxed_1216_ = lean_unbox(v_safety_1209_);
v_checkMeta_boxed_1217_ = lean_unbox(v_checkMeta_1210_);
v_res_1218_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1207_, v_value_1208_, v_safety_boxed_1216_, v_checkMeta_boxed_1217_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1219_, lean_object* v_expectedType_1220_, lean_object* v_value_1221_, uint8_t v_safety_1222_, uint8_t v_checkMeta_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1220_, v_value_1221_, v_safety_1222_, v_checkMeta_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_expectedType_1231_, lean_object* v_value_1232_, lean_object* v_safety_1233_, lean_object* v_checkMeta_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
uint8_t v_safety_boxed_1240_; uint8_t v_checkMeta_boxed_1241_; lean_object* v_res_1242_; 
v_safety_boxed_1240_ = lean_unbox(v_safety_1233_);
v_checkMeta_boxed_1241_ = lean_unbox(v_checkMeta_1234_);
v_res_1242_ = l_Lean_Meta_evalExpr(v_00_u03b1_1230_, v_expectedType_1231_, v_value_1232_, v_safety_boxed_1240_, v_checkMeta_boxed_1241_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1242_;
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

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
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_46_, lean_object* v_opt_47_){
_start:
{
lean_object* v_name_48_; lean_object* v_defValue_49_; lean_object* v_map_50_; lean_object* v___x_51_; 
v_name_48_ = lean_ctor_get(v_opt_47_, 0);
v_defValue_49_ = lean_ctor_get(v_opt_47_, 1);
v_map_50_ = lean_ctor_get(v_opts_46_, 0);
v___x_51_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_50_, v_name_48_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_inc(v_defValue_49_);
return v_defValue_49_;
}
else
{
lean_object* v_val_52_; 
v_val_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v___x_51_, 1);
if (lean_obj_tag(v_val_52_) == 3)
{
lean_object* v_v_53_; 
v_v_53_ = lean_ctor_get(v_val_52_, 0);
lean_inc(v_v_53_);
lean_dec_ref_known(v_val_52_, 1);
return v_v_53_;
}
else
{
lean_dec(v_val_52_);
lean_inc(v_defValue_49_);
return v_defValue_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_54_, lean_object* v_opt_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v_opts_54_, v_opt_55_);
lean_dec_ref(v_opt_55_);
lean_dec_ref(v_opts_54_);
return v_res_56_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v___x_57_, lean_object* v___x_58_, lean_object* v_as_59_, size_t v_i_60_, size_t v_stop_61_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = lean_usize_dec_eq(v_i_60_, v_stop_61_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_uget_borrowed(v_as_59_, v_i_60_);
v___x_68_ = l_Lean_Environment_isImportedConst(v___x_57_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_lt(v___x_69_, v___x_58_);
if (v___x_70_ == 0)
{
goto v___jp_62_;
}
else
{
return v___x_70_;
}
}
else
{
goto v___jp_62_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
v___jp_62_:
{
size_t v___x_63_; size_t v___x_64_; 
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_add(v_i_60_, v___x_63_);
v_i_60_ = v___x_64_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_57_ = stack[0].m_obj;
lean_object* v___x_58_ = stack[1].m_obj;
lean_object* v_as_59_ = stack[2].m_obj;
size_t v_i_60_ = stack[3].m_num;
size_t v_stop_61_ = stack[4].m_num;
uint8_t v_res_72_;
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v___x_57_, v___x_58_, v_as_59_, v_i_60_, v_stop_61_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_as_75_, lean_object* v_i_76_, lean_object* v_stop_77_){
_start:
{
size_t v_i_boxed_78_; size_t v_stop_boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_i_boxed_78_ = lean_unbox_usize(v_i_76_);
lean_dec(v_i_76_);
v_stop_boxed_79_ = lean_unbox_usize(v_stop_77_);
lean_dec(v_stop_77_);
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v___x_73_, v___x_74_, v_as_75_, v_i_boxed_78_, v_stop_boxed_79_);
lean_dec_ref(v_as_75_);
lean_dec(v___x_74_);
lean_dec_ref(v___x_73_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = l_Lean_Elab_abortCommandExceptionId;
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
return v___x_84_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___closed__0);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_88_;
v_res_88_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg___boxed(lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v_res_90_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_env_98_; uint8_t v___x_99_; lean_object* v_env_100_; lean_object* v___x_101_; lean_object* v_toCold_102_; lean_object* v_mctx_103_; lean_object* v_lctx_104_; lean_object* v_options_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = 0;
v_env_100_ = l_Lean_Environment_setRecordingDeps(v_env_98_, v___x_99_);
v___x_101_ = lean_st_ref_get(v___y_93_);
v_toCold_102_ = lean_ctor_get(v___y_94_, 0);
v_mctx_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_mctx_103_);
lean_dec(v___x_101_);
v_lctx_104_ = lean_ctor_get(v___y_92_, 2);
v_options_105_ = lean_ctor_get(v_toCold_102_, 2);
lean_inc_ref(v_options_105_);
lean_inc_ref(v_lctx_104_);
v___x_106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_106_, 0, v_env_100_);
lean_ctor_set(v___x_106_, 1, v_mctx_103_);
lean_ctor_set(v___x_106_, 2, v_lctx_104_);
lean_ctor_set(v___x_106_, 3, v_options_105_);
v___x_107_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_msgData_91_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_91_ = stack[0].m_obj;
lean_object* v___y_92_ = stack[1].m_obj;
lean_object* v___y_93_ = stack[2].m_obj;
lean_object* v___y_94_ = stack[3].m_obj;
lean_object* v___y_95_ = stack[4].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msgData_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_ref_123_; lean_object* v___x_124_; lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_133_; 
v_ref_123_ = lean_ctor_get(v___y_120_, 2);
v___x_124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_133_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_inc(v_ref_123_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ref_123_);
lean_ctor_set(v___x_129_, 1, v_a_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 1);
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_117_ = stack[0].m_obj;
lean_object* v___y_118_ = stack[1].m_obj;
lean_object* v___y_119_ = stack[2].m_obj;
lean_object* v___y_120_ = stack[3].m_obj;
lean_object* v___y_121_ = stack[4].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(lean_object* v_x_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_148_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v_x_142_, 1);
v___x_149_ = l_Lean_stringToMessageData(v_a_148_);
v___x_150_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_149_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_150_;
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v_x_142_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v_x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 0);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[0].m_obj;
lean_object* v___y_143_ = stack[1].m_obj;
lean_object* v___y_144_ = stack[2].m_obj;
lean_object* v___y_145_ = stack[3].m_obj;
lean_object* v___y_146_ = stack[4].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg___boxed(lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_166_;
}
}
lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(lean_object* v_constName_167_, uint8_t v_checkMeta_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; uint8_t v___x_176_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
lean_inc(v_constName_167_);
v___x_176_ = lean_has_compile_error(v_env_175_, v_constName_167_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v_env_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_177_ = lean_st_ref_get(v___y_172_);
v_env_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_env_178_);
lean_dec(v___x_177_);
v___x_179_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_171_);
v___x_180_ = l_Lean_Environment_evalConst___redArg(v_env_178_, v___x_179_, v_constName_167_, v_checkMeta_168_);
lean_dec(v_constName_167_);
lean_dec_ref(v___x_179_);
lean_dec_ref(v_env_178_);
v___x_181_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_180_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; lean_object* v_env_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref_known(v___x_182_, 1);
v___x_183_ = lean_st_ref_get(v___y_172_);
v_env_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc_ref(v_env_184_);
lean_dec(v___x_183_);
v___x_185_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_171_);
v___x_186_ = l_Lean_Environment_evalConst___redArg(v_env_184_, v___x_185_, v_constName_167_, v_checkMeta_168_);
lean_dec(v_constName_167_);
lean_dec_ref(v___x_185_);
lean_dec_ref(v_env_184_);
v___x_187_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v___x_186_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_187_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_constName_167_);
v_a_188_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_182_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_182_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_167_ = stack[0].m_obj;
uint8_t v_checkMeta_168_ = stack[1].m_num;
lean_object* v___y_169_ = stack[2].m_obj;
lean_object* v___y_170_ = stack[3].m_obj;
lean_object* v___y_171_ = stack[4].m_obj;
lean_object* v___y_172_ = stack[5].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_167_, v_checkMeta_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg___boxed(lean_object* v_constName_197_, lean_object* v_checkMeta_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
uint8_t v_checkMeta_boxed_204_; lean_object* v_res_205_; 
v_checkMeta_boxed_204_ = lean_unbox(v_checkMeta_198_);
v_res_205_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_197_, v_checkMeta_boxed_204_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_205_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_o_209_, lean_object* v_k_210_, uint8_t v_v_211_){
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
v___x_219_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___closed__1));
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
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_209_ = stack[0].m_obj;
lean_object* v_k_210_ = stack[1].m_obj;
uint8_t v_v_211_ = stack[2].m_num;
lean_object* v_res_228_;
v_res_228_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_o_209_, v_k_210_, v_v_211_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_o_229_, lean_object* v_k_230_, lean_object* v_v_231_){
_start:
{
uint8_t v_v_boxed_232_; lean_object* v_res_233_; 
v_v_boxed_232_ = lean_unbox(v_v_231_);
v_res_233_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_o_229_, v_k_230_, v_v_boxed_232_);
return v_res_233_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_opts_234_, lean_object* v_opt_235_, uint8_t v_val_236_){
_start:
{
lean_object* v_name_237_; lean_object* v___x_238_; 
v_name_237_ = lean_ctor_get(v_opt_235_, 0);
lean_inc(v_name_237_);
lean_dec_ref(v_opt_235_);
v___x_238_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_opts_234_, v_name_237_, v_val_236_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_234_ = stack[0].m_obj;
lean_object* v_opt_235_ = stack[1].m_obj;
uint8_t v_val_236_ = stack[2].m_num;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_opts_234_, v_opt_235_, v_val_236_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_opts_240_, lean_object* v_opt_241_, lean_object* v_val_242_){
_start:
{
uint8_t v_val_boxed_243_; lean_object* v_res_244_; 
v_val_boxed_243_ = lean_unbox(v_val_242_);
v_res_244_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_opts_240_, v_opt_241_, v_val_boxed_243_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_251_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_ctor_set(v___x_251_, 2, v___x_250_);
lean_ctor_set(v___x_251_, 3, v___x_250_);
lean_ctor_set(v___x_251_, 4, v___x_250_);
lean_ctor_set(v___x_251_, 5, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = lean_unsigned_to_nat(16u);
v___x_258_ = lean_mk_array(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_265_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_270_, lean_object* v_checkType_271_, uint8_t v_safety_272_, lean_object* v_value_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___y_280_; uint8_t v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint16_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; uint16_t v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; uint8_t v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; uint16_t v___y_373_; lean_object* v___y_374_; uint8_t v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; uint8_t v___y_406_; uint16_t v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; uint8_t v___y_457_; uint8_t v___y_458_; uint16_t v___y_459_; uint8_t v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; uint16_t v___y_492_; uint8_t v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; uint8_t v___y_498_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; uint8_t v___y_504_; uint8_t v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; uint16_t v___y_523_; uint8_t v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint16_t v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; uint8_t v___y_576_; uint8_t v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; uint16_t v___y_607_; uint8_t v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; uint8_t v___y_613_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; uint8_t v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v_nextMacroScope_767_; lean_object* v_ngen_768_; lean_object* v_auxDeclNGen_769_; lean_object* v_traceState_770_; lean_object* v_recordedDeps_771_; lean_object* v_messages_772_; lean_object* v_infoState_773_; lean_object* v_snapshotTasks_774_; lean_object* v___y_775_; lean_object* v___x_794_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_794_ = lean_st_ref_get(v___y_277_);
lean_inc_ref(v_value_273_);
v___x_808_ = l_Lean_Expr_getUsedConstants(v_value_273_);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_array_get_size(v___x_808_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec_ref(v___x_808_);
lean_dec(v___x_794_);
goto v___jp_795_;
}
else
{
if (v___x_811_ == 0)
{
lean_dec_ref(v___x_808_);
lean_dec(v___x_794_);
goto v___jp_795_;
}
else
{
lean_object* v_env_812_; size_t v___x_813_; size_t v___x_814_; uint8_t v___x_815_; 
v_env_812_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_env_812_);
lean_dec(v___x_794_);
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_810_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v_env_812_, v___x_810_, v___x_808_, v___x_813_, v___x_814_);
lean_dec_ref(v___x_808_);
lean_dec_ref(v_env_812_);
if (v___x_815_ == 0)
{
goto v___jp_795_;
}
else
{
goto v___jp_724_;
}
}
}
v___jp_279_:
{
lean_object* v_toCold_291_; lean_object* v_currRecDepth_292_; lean_object* v_ref_293_; uint8_t v_suppressElabErrors_294_; uint8_t v_isRecordingDeps_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_332_; 
v_toCold_291_ = lean_ctor_get(v___y_289_, 0);
v_currRecDepth_292_ = lean_ctor_get(v___y_289_, 1);
v_ref_293_ = lean_ctor_get(v___y_289_, 2);
v_suppressElabErrors_294_ = lean_ctor_get_uint8(v___y_289_, sizeof(void*)*3 + 2);
v_isRecordingDeps_295_ = lean_ctor_get_uint8(v___y_289_, sizeof(void*)*3 + 3);
v_isSharedCheck_332_ = !lean_is_exclusive(v___y_289_);
if (v_isSharedCheck_332_ == 0)
{
v___x_297_ = v___y_289_;
v_isShared_298_ = v_isSharedCheck_332_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_ref_293_);
lean_inc(v_currRecDepth_292_);
lean_inc(v_toCold_291_);
lean_dec(v___y_289_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_332_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_fileName_299_; lean_object* v_fileMap_300_; lean_object* v_currNamespace_301_; lean_object* v_openDecls_302_; lean_object* v_initHeartbeats_303_; lean_object* v_maxHeartbeats_304_; lean_object* v_quotContext_305_; lean_object* v_currMacroScope_306_; lean_object* v_cancelTk_x3f_307_; lean_object* v_inheritedTraceOptions_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_329_; 
v_fileName_299_ = lean_ctor_get(v_toCold_291_, 0);
v_fileMap_300_ = lean_ctor_get(v_toCold_291_, 1);
v_currNamespace_301_ = lean_ctor_get(v_toCold_291_, 4);
v_openDecls_302_ = lean_ctor_get(v_toCold_291_, 5);
v_initHeartbeats_303_ = lean_ctor_get(v_toCold_291_, 6);
v_maxHeartbeats_304_ = lean_ctor_get(v_toCold_291_, 7);
v_quotContext_305_ = lean_ctor_get(v_toCold_291_, 8);
v_currMacroScope_306_ = lean_ctor_get(v_toCold_291_, 9);
v_cancelTk_x3f_307_ = lean_ctor_get(v_toCold_291_, 10);
v_inheritedTraceOptions_308_ = lean_ctor_get(v_toCold_291_, 11);
v_isSharedCheck_329_ = !lean_is_exclusive(v_toCold_291_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_330_ = lean_ctor_get(v_toCold_291_, 3);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_toCold_291_, 2);
lean_dec(v_unused_331_);
v___x_310_ = v_toCold_291_;
v_isShared_311_ = v_isSharedCheck_329_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_inheritedTraceOptions_308_);
lean_inc(v_cancelTk_x3f_307_);
lean_inc(v_currMacroScope_306_);
lean_inc(v_quotContext_305_);
lean_inc(v_maxHeartbeats_304_);
lean_inc(v_initHeartbeats_303_);
lean_inc(v_openDecls_302_);
lean_inc(v_currNamespace_301_);
lean_inc(v_fileMap_300_);
lean_inc(v_fileName_299_);
lean_dec(v_toCold_291_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_329_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_285_, v___y_287_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v___x_312_);
lean_ctor_set(v___x_310_, 2, v___y_285_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_fileName_299_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_fileMap_300_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v___y_285_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_currNamespace_301_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_openDecls_302_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_initHeartbeats_303_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_maxHeartbeats_304_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_quotContext_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 9, v_currMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 10, v_cancelTk_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_328_, 11, v_inheritedTraceOptions_308_);
v___x_314_ = v_reuseFailAlloc_328_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_314_);
v___x_316_ = v___x_297_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_currRecDepth_292_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_ref_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*3 + 2, v_suppressElabErrors_294_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*3 + 3, v_isRecordingDeps_295_);
v___x_316_ = v_reuseFailAlloc_327_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
lean_ctor_set_uint16(v___x_316_, sizeof(void*)*3, v___y_288_);
v___x_317_ = l_Lean_addAndCompile(v___y_284_, v___y_282_, v___y_281_, v___x_316_, v___y_290_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; 
lean_dec_ref_known(v___x_317_, 1);
v___x_318_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v___y_280_, v_checkMeta_270_, v___y_283_, v___y_286_, v___x_316_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___x_316_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_283_);
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v___x_316_);
lean_dec(v___y_290_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_280_);
v_a_319_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_317_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
}
}
v___jp_333_:
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_ngen_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_traceState_352_; lean_object* v_recordedDeps_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
v___x_347_ = lean_st_ref_take(v___y_336_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_347_, 1);
v_ngen_350_ = lean_ctor_get(v___x_347_, 2);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_347_, 3);
v_traceState_352_ = lean_ctor_get(v___x_347_, 4);
v_recordedDeps_353_ = lean_ctor_get(v___x_347_, 6);
v_messages_354_ = lean_ctor_get(v___x_347_, 7);
v_infoState_355_ = lean_ctor_get(v___x_347_, 8);
v_snapshotTasks_356_ = lean_ctor_get(v___x_347_, 9);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_347_, 5);
lean_dec(v_unused_366_);
v___x_358_ = v___x_347_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_recordedDeps_353_);
lean_inc(v_traceState_352_);
lean_inc(v_auxDeclNGen_351_);
lean_inc(v_ngen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_347_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = l_Lean_Kernel_enableDiag(v_env_348_, v___y_337_);
lean_inc_ref(v___y_341_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 5, v___y_341_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v___y_341_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_recordedDeps_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 9, v_snapshotTasks_356_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_st_ref_put(v___y_336_, v___x_362_);
v___y_280_ = v___y_335_;
v___y_281_ = v___y_342_;
v___y_282_ = v___y_343_;
v___y_283_ = v___y_338_;
v___y_284_ = v___y_344_;
v___y_285_ = v___y_339_;
v___y_286_ = v___y_345_;
v___y_287_ = v___y_346_;
v___y_288_ = v___y_340_;
v___y_289_ = v___y_334_;
v___y_290_ = v___y_336_;
goto v___jp_279_;
}
}
}
v___jp_367_:
{
if (v___y_381_ == 0)
{
if (v___y_378_ == 0)
{
v___y_280_ = v___y_369_;
v___y_281_ = v___y_375_;
v___y_282_ = v___y_376_;
v___y_283_ = v___y_371_;
v___y_284_ = v___y_377_;
v___y_285_ = v___y_372_;
v___y_286_ = v___y_379_;
v___y_287_ = v___y_380_;
v___y_288_ = v___y_373_;
v___y_289_ = v___y_368_;
v___y_290_ = v___y_370_;
goto v___jp_279_;
}
else
{
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_381_;
v___y_338_ = v___y_371_;
v___y_339_ = v___y_372_;
v___y_340_ = v___y_373_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_375_;
v___y_343_ = v___y_376_;
v___y_344_ = v___y_377_;
v___y_345_ = v___y_379_;
v___y_346_ = v___y_380_;
goto v___jp_333_;
}
}
else
{
if (v___y_378_ == 0)
{
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_381_;
v___y_338_ = v___y_371_;
v___y_339_ = v___y_372_;
v___y_340_ = v___y_373_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_375_;
v___y_343_ = v___y_376_;
v___y_344_ = v___y_377_;
v___y_345_ = v___y_379_;
v___y_346_ = v___y_380_;
goto v___jp_333_;
}
else
{
v___y_280_ = v___y_369_;
v___y_281_ = v___y_375_;
v___y_282_ = v___y_376_;
v___y_283_ = v___y_371_;
v___y_284_ = v___y_377_;
v___y_285_ = v___y_372_;
v___y_286_ = v___y_379_;
v___y_287_ = v___y_380_;
v___y_288_ = v___y_373_;
v___y_289_ = v___y_368_;
v___y_290_ = v___y_370_;
goto v___jp_279_;
}
}
}
v___jp_382_:
{
uint16_t v___x_394_; lean_object* v___x_395_; lean_object* v_env_396_; uint8_t v___x_397_; uint16_t v___x_398_; uint16_t v___x_399_; uint16_t v___x_400_; uint8_t v___x_401_; 
v___x_394_ = l_Lean_OptionFlags_ofOptions(v___y_393_);
v___x_395_ = lean_st_ref_get(v___y_386_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v___x_397_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_396_);
lean_dec_ref(v_env_396_);
v___x_398_ = 512;
v___x_399_ = lean_uint16_land(v___x_394_, v___x_398_);
v___x_400_ = 0;
v___x_401_ = lean_uint16_dec_eq(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
v___y_368_ = v___y_384_;
v___y_369_ = v___y_385_;
v___y_370_ = v___y_386_;
v___y_371_ = v___y_390_;
v___y_372_ = v___y_393_;
v___y_373_ = v___x_394_;
v___y_374_ = v___y_383_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_389_;
v___y_378_ = v___x_397_;
v___y_379_ = v___y_392_;
v___y_380_ = v___y_391_;
v___y_381_ = v___y_388_;
goto v___jp_367_;
}
else
{
v___y_368_ = v___y_384_;
v___y_369_ = v___y_385_;
v___y_370_ = v___y_386_;
v___y_371_ = v___y_390_;
v___y_372_ = v___y_393_;
v___y_373_ = v___x_394_;
v___y_374_ = v___y_383_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_389_;
v___y_378_ = v___x_397_;
v___y_379_ = v___y_392_;
v___y_380_ = v___y_391_;
v___y_381_ = v___y_387_;
goto v___jp_367_;
}
}
v___jp_402_:
{
lean_object* v_toCold_415_; lean_object* v_currRecDepth_416_; lean_object* v_ref_417_; uint8_t v_suppressElabErrors_418_; uint8_t v_isRecordingDeps_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_449_; 
v_toCold_415_ = lean_ctor_get(v___y_413_, 0);
v_currRecDepth_416_ = lean_ctor_get(v___y_413_, 1);
v_ref_417_ = lean_ctor_get(v___y_413_, 2);
v_suppressElabErrors_418_ = lean_ctor_get_uint8(v___y_413_, sizeof(void*)*3 + 2);
v_isRecordingDeps_419_ = lean_ctor_get_uint8(v___y_413_, sizeof(void*)*3 + 3);
v_isSharedCheck_449_ = !lean_is_exclusive(v___y_413_);
if (v_isSharedCheck_449_ == 0)
{
v___x_421_ = v___y_413_;
v_isShared_422_ = v_isSharedCheck_449_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_ref_417_);
lean_inc(v_currRecDepth_416_);
lean_inc(v_toCold_415_);
lean_dec(v___y_413_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_449_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_fileName_423_; lean_object* v_fileMap_424_; lean_object* v_currNamespace_425_; lean_object* v_openDecls_426_; lean_object* v_initHeartbeats_427_; lean_object* v_maxHeartbeats_428_; lean_object* v_quotContext_429_; lean_object* v_currMacroScope_430_; lean_object* v_cancelTk_x3f_431_; lean_object* v_inheritedTraceOptions_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_446_; 
v_fileName_423_ = lean_ctor_get(v_toCold_415_, 0);
v_fileMap_424_ = lean_ctor_get(v_toCold_415_, 1);
v_currNamespace_425_ = lean_ctor_get(v_toCold_415_, 4);
v_openDecls_426_ = lean_ctor_get(v_toCold_415_, 5);
v_initHeartbeats_427_ = lean_ctor_get(v_toCold_415_, 6);
v_maxHeartbeats_428_ = lean_ctor_get(v_toCold_415_, 7);
v_quotContext_429_ = lean_ctor_get(v_toCold_415_, 8);
v_currMacroScope_430_ = lean_ctor_get(v_toCold_415_, 9);
v_cancelTk_x3f_431_ = lean_ctor_get(v_toCold_415_, 10);
v_inheritedTraceOptions_432_ = lean_ctor_get(v_toCold_415_, 11);
v_isSharedCheck_446_ = !lean_is_exclusive(v_toCold_415_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_447_ = lean_ctor_get(v_toCold_415_, 3);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_toCold_415_, 2);
lean_dec(v_unused_448_);
v___x_434_ = v_toCold_415_;
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_inheritedTraceOptions_432_);
lean_inc(v_cancelTk_x3f_431_);
lean_inc(v_currMacroScope_430_);
lean_inc(v_quotContext_429_);
lean_inc(v_maxHeartbeats_428_);
lean_inc(v_initHeartbeats_427_);
lean_inc(v_openDecls_426_);
lean_inc(v_currNamespace_425_);
lean_inc(v_fileMap_424_);
lean_inc(v_fileName_423_);
lean_dec(v_toCold_415_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_404_, v___y_412_);
lean_inc_ref(v___y_404_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 3, v___x_436_);
lean_ctor_set(v___x_434_, 2, v___y_404_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fileName_423_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_fileMap_424_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___y_404_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_currNamespace_425_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_openDecls_426_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_initHeartbeats_427_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_maxHeartbeats_428_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_quotContext_429_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_currMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 10, v_cancelTk_x3f_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 11, v_inheritedTraceOptions_432_);
v___x_438_ = v_reuseFailAlloc_445_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_438_);
v___x_440_ = v___x_421_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_currRecDepth_416_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_ref_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*3 + 2, v_suppressElabErrors_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*3 + 3, v_isRecordingDeps_419_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_ctor_set_uint16(v___x_440_, sizeof(void*)*3, v___y_407_);
if (v_isRecordingDeps_419_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_442_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_404_, v___x_441_, v___y_408_);
v___y_383_ = v___y_403_;
v___y_384_ = v___x_440_;
v___y_385_ = v___y_405_;
v___y_386_ = v___y_414_;
v___y_387_ = v___y_406_;
v___y_388_ = v___y_408_;
v___y_389_ = v___y_410_;
v___y_390_ = v___y_409_;
v___y_391_ = v___y_412_;
v___y_392_ = v___y_411_;
v___y_393_ = v___x_442_;
goto v___jp_382_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_404_);
v___y_383_ = v___y_403_;
v___y_384_ = v___x_440_;
v___y_385_ = v___y_405_;
v___y_386_ = v___y_414_;
v___y_387_ = v___y_406_;
v___y_388_ = v___y_408_;
v___y_389_ = v___y_410_;
v___y_390_ = v___y_409_;
v___y_391_ = v___y_412_;
v___y_392_ = v___y_411_;
v___y_393_ = v___x_443_;
goto v___jp_382_;
}
}
}
}
}
}
v___jp_450_:
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v_nextMacroScope_466_; lean_object* v_ngen_467_; lean_object* v_auxDeclNGen_468_; lean_object* v_traceState_469_; lean_object* v_recordedDeps_470_; lean_object* v_messages_471_; lean_object* v_infoState_472_; lean_object* v_snapshotTasks_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v___x_464_ = lean_st_ref_take(v___y_456_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
v_nextMacroScope_466_ = lean_ctor_get(v___x_464_, 1);
v_ngen_467_ = lean_ctor_get(v___x_464_, 2);
v_auxDeclNGen_468_ = lean_ctor_get(v___x_464_, 3);
v_traceState_469_ = lean_ctor_get(v___x_464_, 4);
v_recordedDeps_470_ = lean_ctor_get(v___x_464_, 6);
v_messages_471_ = lean_ctor_get(v___x_464_, 7);
v_infoState_472_ = lean_ctor_get(v___x_464_, 8);
v_snapshotTasks_473_ = lean_ctor_get(v___x_464_, 9);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_464_, 5);
lean_dec(v_unused_483_);
v___x_475_ = v___x_464_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snapshotTasks_473_);
lean_inc(v_infoState_472_);
lean_inc(v_messages_471_);
lean_inc(v_recordedDeps_470_);
lean_inc(v_traceState_469_);
lean_inc(v_auxDeclNGen_468_);
lean_inc(v_ngen_467_);
lean_inc(v_nextMacroScope_466_);
lean_inc(v_env_465_);
lean_dec(v___x_464_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_Kernel_enableDiag(v_env_465_, v___y_457_);
lean_inc_ref(v___y_455_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 5, v___y_455_);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_468_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_traceState_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v___y_455_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_recordedDeps_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_messages_471_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_infoState_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_snapshotTasks_473_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; 
v___x_480_ = lean_st_ref_put(v___y_456_, v___x_479_);
v___y_403_ = v___y_455_;
v___y_404_ = v___y_451_;
v___y_405_ = v___y_452_;
v___y_406_ = v___y_458_;
v___y_407_ = v___y_459_;
v___y_408_ = v___y_460_;
v___y_409_ = v___y_454_;
v___y_410_ = v___y_461_;
v___y_411_ = v___y_463_;
v___y_412_ = v___y_462_;
v___y_413_ = v___y_453_;
v___y_414_ = v___y_456_;
goto v___jp_402_;
}
}
}
v___jp_484_:
{
if (v___y_498_ == 0)
{
if (v___y_497_ == 0)
{
v___y_403_ = v___y_489_;
v___y_404_ = v___y_485_;
v___y_405_ = v___y_486_;
v___y_406_ = v___y_491_;
v___y_407_ = v___y_492_;
v___y_408_ = v___y_493_;
v___y_409_ = v___y_488_;
v___y_410_ = v___y_494_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_495_;
v___y_413_ = v___y_487_;
v___y_414_ = v___y_490_;
goto v___jp_402_;
}
else
{
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_491_;
v___y_459_ = v___y_492_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_494_;
v___y_462_ = v___y_495_;
v___y_463_ = v___y_496_;
goto v___jp_450_;
}
}
else
{
if (v___y_497_ == 0)
{
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_491_;
v___y_459_ = v___y_492_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_494_;
v___y_462_ = v___y_495_;
v___y_463_ = v___y_496_;
goto v___jp_450_;
}
else
{
v___y_403_ = v___y_489_;
v___y_404_ = v___y_485_;
v___y_405_ = v___y_486_;
v___y_406_ = v___y_491_;
v___y_407_ = v___y_492_;
v___y_408_ = v___y_493_;
v___y_409_ = v___y_488_;
v___y_410_ = v___y_494_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_495_;
v___y_413_ = v___y_487_;
v___y_414_ = v___y_490_;
goto v___jp_402_;
}
}
}
v___jp_499_:
{
uint16_t v___x_511_; lean_object* v___x_512_; lean_object* v_env_513_; uint8_t v___x_514_; uint16_t v___x_515_; uint16_t v___x_516_; uint16_t v___x_517_; uint8_t v___x_518_; 
v___x_511_ = l_Lean_OptionFlags_ofOptions(v___y_510_);
v___x_512_ = lean_st_ref_get(v___y_503_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_513_);
lean_dec_ref(v_env_513_);
v___x_515_ = 512;
v___x_516_ = lean_uint16_land(v___x_511_, v___x_515_);
v___x_517_ = 0;
v___x_518_ = lean_uint16_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
v___y_485_ = v___y_510_;
v___y_486_ = v___y_501_;
v___y_487_ = v___y_502_;
v___y_488_ = v___y_507_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_503_;
v___y_491_ = v___y_504_;
v___y_492_ = v___x_511_;
v___y_493_ = v___y_505_;
v___y_494_ = v___y_506_;
v___y_495_ = v___y_508_;
v___y_496_ = v___y_509_;
v___y_497_ = v___x_514_;
v___y_498_ = v___y_505_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___y_510_;
v___y_486_ = v___y_501_;
v___y_487_ = v___y_502_;
v___y_488_ = v___y_507_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_503_;
v___y_491_ = v___y_504_;
v___y_492_ = v___x_511_;
v___y_493_ = v___y_505_;
v___y_494_ = v___y_506_;
v___y_495_ = v___y_508_;
v___y_496_ = v___y_509_;
v___y_497_ = v___x_514_;
v___y_498_ = v___y_504_;
goto v___jp_484_;
}
}
v___jp_519_:
{
lean_object* v_toCold_531_; lean_object* v_currRecDepth_532_; lean_object* v_ref_533_; uint8_t v_suppressElabErrors_534_; uint8_t v_isRecordingDeps_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_566_; 
v_toCold_531_ = lean_ctor_get(v___y_529_, 0);
v_currRecDepth_532_ = lean_ctor_get(v___y_529_, 1);
v_ref_533_ = lean_ctor_get(v___y_529_, 2);
v_suppressElabErrors_534_ = lean_ctor_get_uint8(v___y_529_, sizeof(void*)*3 + 2);
v_isRecordingDeps_535_ = lean_ctor_get_uint8(v___y_529_, sizeof(void*)*3 + 3);
v_isSharedCheck_566_ = !lean_is_exclusive(v___y_529_);
if (v_isSharedCheck_566_ == 0)
{
v___x_537_ = v___y_529_;
v_isShared_538_ = v_isSharedCheck_566_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_ref_533_);
lean_inc(v_currRecDepth_532_);
lean_inc(v_toCold_531_);
lean_dec(v___y_529_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_566_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_fileName_539_; lean_object* v_fileMap_540_; lean_object* v_currNamespace_541_; lean_object* v_openDecls_542_; lean_object* v_initHeartbeats_543_; lean_object* v_maxHeartbeats_544_; lean_object* v_quotContext_545_; lean_object* v_currMacroScope_546_; lean_object* v_cancelTk_x3f_547_; lean_object* v_inheritedTraceOptions_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_563_; 
v_fileName_539_ = lean_ctor_get(v_toCold_531_, 0);
v_fileMap_540_ = lean_ctor_get(v_toCold_531_, 1);
v_currNamespace_541_ = lean_ctor_get(v_toCold_531_, 4);
v_openDecls_542_ = lean_ctor_get(v_toCold_531_, 5);
v_initHeartbeats_543_ = lean_ctor_get(v_toCold_531_, 6);
v_maxHeartbeats_544_ = lean_ctor_get(v_toCold_531_, 7);
v_quotContext_545_ = lean_ctor_get(v_toCold_531_, 8);
v_currMacroScope_546_ = lean_ctor_get(v_toCold_531_, 9);
v_cancelTk_x3f_547_ = lean_ctor_get(v_toCold_531_, 10);
v_inheritedTraceOptions_548_ = lean_ctor_get(v_toCold_531_, 11);
v_isSharedCheck_563_ = !lean_is_exclusive(v_toCold_531_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; 
v_unused_564_ = lean_ctor_get(v_toCold_531_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_toCold_531_, 2);
lean_dec(v_unused_565_);
v___x_550_ = v_toCold_531_;
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_inheritedTraceOptions_548_);
lean_inc(v_cancelTk_x3f_547_);
lean_inc(v_currMacroScope_546_);
lean_inc(v_quotContext_545_);
lean_inc(v_maxHeartbeats_544_);
lean_inc(v_initHeartbeats_543_);
lean_inc(v_openDecls_542_);
lean_inc(v_currNamespace_541_);
lean_inc(v_fileMap_540_);
lean_inc(v_fileName_539_);
lean_dec(v_toCold_531_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_563_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = l_Lean_maxRecDepth;
v___x_553_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_521_, v___x_552_);
lean_inc_ref(v___y_521_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 3, v___x_553_);
lean_ctor_set(v___x_550_, 2, v___y_521_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fileName_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_fileMap_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___y_521_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_currNamespace_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_openDecls_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_initHeartbeats_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_maxHeartbeats_544_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v_quotContext_545_);
lean_ctor_set(v_reuseFailAlloc_562_, 9, v_currMacroScope_546_);
lean_ctor_set(v_reuseFailAlloc_562_, 10, v_cancelTk_x3f_547_);
lean_ctor_set(v_reuseFailAlloc_562_, 11, v_inheritedTraceOptions_548_);
v___x_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_555_);
v___x_557_ = v___x_537_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_currRecDepth_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ref_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_561_, sizeof(void*)*3 + 2, v_suppressElabErrors_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_561_, sizeof(void*)*3 + 3, v_isRecordingDeps_535_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_uint16(v___x_557_, sizeof(void*)*3, v___y_523_);
if (v_isRecordingDeps_535_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_559_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_521_, v___x_558_, v_isRecordingDeps_535_);
v___y_500_ = v___y_520_;
v___y_501_ = v___y_522_;
v___y_502_ = v___x_557_;
v___y_503_ = v___y_530_;
v___y_504_ = v___y_524_;
v___y_505_ = v___y_525_;
v___y_506_ = v___y_527_;
v___y_507_ = v___y_526_;
v___y_508_ = v___x_552_;
v___y_509_ = v___y_528_;
v___y_510_ = v___x_559_;
goto v___jp_499_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_521_);
v___y_500_ = v___y_520_;
v___y_501_ = v___y_522_;
v___y_502_ = v___x_557_;
v___y_503_ = v___y_530_;
v___y_504_ = v___y_524_;
v___y_505_ = v___y_525_;
v___y_506_ = v___y_527_;
v___y_507_ = v___y_526_;
v___y_508_ = v___x_552_;
v___y_509_ = v___y_528_;
v___y_510_ = v___x_560_;
goto v___jp_499_;
}
}
}
}
}
}
v___jp_567_:
{
lean_object* v___x_580_; lean_object* v_env_581_; lean_object* v_nextMacroScope_582_; lean_object* v_ngen_583_; lean_object* v_auxDeclNGen_584_; lean_object* v_traceState_585_; lean_object* v_recordedDeps_586_; lean_object* v_messages_587_; lean_object* v_infoState_588_; lean_object* v_snapshotTasks_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_598_; 
v___x_580_ = lean_st_ref_take(v___y_575_);
v_env_581_ = lean_ctor_get(v___x_580_, 0);
v_nextMacroScope_582_ = lean_ctor_get(v___x_580_, 1);
v_ngen_583_ = lean_ctor_get(v___x_580_, 2);
v_auxDeclNGen_584_ = lean_ctor_get(v___x_580_, 3);
v_traceState_585_ = lean_ctor_get(v___x_580_, 4);
v_recordedDeps_586_ = lean_ctor_get(v___x_580_, 6);
v_messages_587_ = lean_ctor_get(v___x_580_, 7);
v_infoState_588_ = lean_ctor_get(v___x_580_, 8);
v_snapshotTasks_589_ = lean_ctor_get(v___x_580_, 9);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_580_, 5);
lean_dec(v_unused_599_);
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_598_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snapshotTasks_589_);
lean_inc(v_infoState_588_);
lean_inc(v_messages_587_);
lean_inc(v_recordedDeps_586_);
lean_inc(v_traceState_585_);
lean_inc(v_auxDeclNGen_584_);
lean_inc(v_ngen_583_);
lean_inc(v_nextMacroScope_582_);
lean_inc(v_env_581_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_598_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_Kernel_enableDiag(v_env_581_, v___y_576_);
lean_inc_ref(v___y_572_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 5, v___y_572_);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_nextMacroScope_582_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_ngen_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_auxDeclNGen_584_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_traceState_585_);
lean_ctor_set(v_reuseFailAlloc_597_, 5, v___y_572_);
lean_ctor_set(v_reuseFailAlloc_597_, 6, v_recordedDeps_586_);
lean_ctor_set(v_reuseFailAlloc_597_, 7, v_messages_587_);
lean_ctor_set(v_reuseFailAlloc_597_, 8, v_infoState_588_);
lean_ctor_set(v_reuseFailAlloc_597_, 9, v_snapshotTasks_589_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_st_ref_put(v___y_575_, v___x_595_);
v___y_520_ = v___y_572_;
v___y_521_ = v___y_568_;
v___y_522_ = v___y_569_;
v___y_523_ = v___y_573_;
v___y_524_ = v___y_574_;
v___y_525_ = v___y_577_;
v___y_526_ = v___y_571_;
v___y_527_ = v___y_578_;
v___y_528_ = v___y_579_;
v___y_529_ = v___y_570_;
v___y_530_ = v___y_575_;
goto v___jp_519_;
}
}
}
v___jp_600_:
{
if (v___y_613_ == 0)
{
if (v___y_606_ == 0)
{
v___y_520_ = v___y_605_;
v___y_521_ = v___y_601_;
v___y_522_ = v___y_602_;
v___y_523_ = v___y_607_;
v___y_524_ = v___y_608_;
v___y_525_ = v___y_610_;
v___y_526_ = v___y_604_;
v___y_527_ = v___y_611_;
v___y_528_ = v___y_612_;
v___y_529_ = v___y_603_;
v___y_530_ = v___y_609_;
goto v___jp_519_;
}
else
{
v___y_568_ = v___y_601_;
v___y_569_ = v___y_602_;
v___y_570_ = v___y_603_;
v___y_571_ = v___y_604_;
v___y_572_ = v___y_605_;
v___y_573_ = v___y_607_;
v___y_574_ = v___y_608_;
v___y_575_ = v___y_609_;
v___y_576_ = v___y_613_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
goto v___jp_567_;
}
}
else
{
if (v___y_606_ == 0)
{
v___y_568_ = v___y_601_;
v___y_569_ = v___y_602_;
v___y_570_ = v___y_603_;
v___y_571_ = v___y_604_;
v___y_572_ = v___y_605_;
v___y_573_ = v___y_607_;
v___y_574_ = v___y_608_;
v___y_575_ = v___y_609_;
v___y_576_ = v___y_613_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
goto v___jp_567_;
}
else
{
v___y_520_ = v___y_605_;
v___y_521_ = v___y_601_;
v___y_522_ = v___y_602_;
v___y_523_ = v___y_607_;
v___y_524_ = v___y_608_;
v___y_525_ = v___y_610_;
v___y_526_ = v___y_604_;
v___y_527_ = v___y_611_;
v___y_528_ = v___y_612_;
v___y_529_ = v___y_603_;
v___y_530_ = v___y_609_;
goto v___jp_519_;
}
}
}
v___jp_614_:
{
uint16_t v___x_625_; lean_object* v___x_626_; lean_object* v_env_627_; uint8_t v___x_628_; uint16_t v___x_629_; uint16_t v___x_630_; uint16_t v___x_631_; uint8_t v___x_632_; 
v___x_625_ = l_Lean_OptionFlags_ofOptions(v___y_624_);
v___x_626_ = lean_st_ref_get(v___y_619_);
v_env_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_626_);
v___x_628_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_627_);
lean_dec_ref(v_env_627_);
v___x_629_ = 512;
v___x_630_ = lean_uint16_land(v___x_625_, v___x_629_);
v___x_631_ = 0;
v___x_632_ = lean_uint16_dec_eq(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
v___y_601_ = v___y_624_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_617_;
v___y_604_ = v___y_622_;
v___y_605_ = v___y_615_;
v___y_606_ = v___x_628_;
v___y_607_ = v___x_625_;
v___y_608_ = v___y_618_;
v___y_609_ = v___y_619_;
v___y_610_ = v___y_620_;
v___y_611_ = v___y_621_;
v___y_612_ = v___y_623_;
v___y_613_ = v___y_620_;
goto v___jp_600_;
}
else
{
v___y_601_ = v___y_624_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_617_;
v___y_604_ = v___y_622_;
v___y_605_ = v___y_615_;
v___y_606_ = v___x_628_;
v___y_607_ = v___x_625_;
v___y_608_ = v___y_618_;
v___y_609_ = v___y_619_;
v___y_610_ = v___y_620_;
v___y_611_ = v___y_621_;
v___y_612_ = v___y_623_;
v___y_613_ = v___y_618_;
goto v___jp_600_;
}
}
v___jp_633_:
{
lean_object* v___x_642_; 
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc_ref(v___y_635_);
v___x_642_ = lean_infer_type(v___y_635_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_n(v_a_643_, 2);
lean_dec_ref_known(v___x_642_, 1);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
v___x_644_ = lean_apply_6(v_checkType_271_, v_a_643_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_env_652_; lean_object* v_nextMacroScope_653_; lean_object* v_ngen_654_; lean_object* v_auxDeclNGen_655_; lean_object* v_traceState_656_; lean_object* v_recordedDeps_657_; lean_object* v_messages_658_; lean_object* v_infoState_659_; lean_object* v_snapshotTasks_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref_known(v___x_644_, 1);
v___x_645_ = lean_array_to_list(v___y_637_);
lean_inc_n(v___y_634_, 2);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v___y_634_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v_a_643_);
v___x_647_ = lean_box(0);
lean_inc(v___y_636_);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_634_);
lean_ctor_set(v___x_648_, 1, v___y_636_);
v___x_649_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_649_, 0, v___x_646_);
lean_ctor_set(v___x_649_, 1, v___y_635_);
lean_ctor_set(v___x_649_, 2, v___x_647_);
lean_ctor_set(v___x_649_, 3, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*4, v_safety_272_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_st_ref_take(v___y_641_);
v_env_652_ = lean_ctor_get(v___x_651_, 0);
v_nextMacroScope_653_ = lean_ctor_get(v___x_651_, 1);
v_ngen_654_ = lean_ctor_get(v___x_651_, 2);
v_auxDeclNGen_655_ = lean_ctor_get(v___x_651_, 3);
v_traceState_656_ = lean_ctor_get(v___x_651_, 4);
v_recordedDeps_657_ = lean_ctor_get(v___x_651_, 6);
v_messages_658_ = lean_ctor_get(v___x_651_, 7);
v_infoState_659_ = lean_ctor_get(v___x_651_, 8);
v_snapshotTasks_660_ = lean_ctor_get(v___x_651_, 9);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_651_, 5);
lean_dec(v_unused_707_);
v___x_662_ = v___x_651_;
v_isShared_663_ = v_isSharedCheck_706_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snapshotTasks_660_);
lean_inc(v_infoState_659_);
lean_inc(v_messages_658_);
lean_inc(v_recordedDeps_657_);
lean_inc(v_traceState_656_);
lean_inc(v_auxDeclNGen_655_);
lean_inc(v_ngen_654_);
lean_inc(v_nextMacroScope_653_);
lean_inc(v_env_652_);
lean_dec(v___x_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_706_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v___y_634_);
v___x_664_ = l_Lean_markMeta(v_env_652_, v___y_634_);
v___x_665_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 5, v___x_665_);
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_nextMacroScope_653_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_ngen_654_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_auxDeclNGen_655_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_traceState_656_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_705_, 6, v_recordedDeps_657_);
lean_ctor_set(v_reuseFailAlloc_705_, 7, v_messages_658_);
lean_ctor_set(v_reuseFailAlloc_705_, 8, v_infoState_659_);
lean_ctor_set(v_reuseFailAlloc_705_, 9, v_snapshotTasks_660_);
v___x_667_ = v_reuseFailAlloc_705_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_mctx_670_; lean_object* v_zetaDeltaFVarIds_671_; lean_object* v_postponed_672_; lean_object* v_diag_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_703_; 
v___x_668_ = lean_st_ref_put(v___y_641_, v___x_667_);
v___x_669_ = lean_st_ref_take(v___y_639_);
v_mctx_670_ = lean_ctor_get(v___x_669_, 0);
v_zetaDeltaFVarIds_671_ = lean_ctor_get(v___x_669_, 2);
v_postponed_672_ = lean_ctor_get(v___x_669_, 3);
v_diag_673_ = lean_ctor_get(v___x_669_, 4);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_669_, 1);
lean_dec(v_unused_704_);
v___x_675_ = v___x_669_;
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_diag_673_);
lean_inc(v_postponed_672_);
lean_inc(v_zetaDeltaFVarIds_671_);
lean_inc(v_mctx_670_);
lean_dec(v___x_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_mctx_670_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_zetaDeltaFVarIds_671_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_postponed_672_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_diag_673_);
v___x_679_ = v_reuseFailAlloc_702_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_env_682_; lean_object* v_checked_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = lean_st_ref_put(v___y_639_, v___x_679_);
v___x_681_ = lean_st_ref_get(v___y_641_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_env_682_);
lean_dec(v___x_681_);
v_checked_683_ = lean_ctor_get(v_env_682_, 2);
lean_inc_ref(v_checked_683_);
lean_dec_ref(v_env_682_);
v___x_684_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_685_ = l_Lean_traceBlock___redArg(v___x_684_, v_checked_683_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_toCold_686_; uint8_t v_isRecordingDeps_687_; lean_object* v_options_688_; uint8_t v___x_689_; uint8_t v___x_690_; 
lean_dec_ref_known(v___x_685_, 1);
v_toCold_686_ = lean_ctor_get(v___y_640_, 0);
v_isRecordingDeps_687_ = lean_ctor_get_uint8(v___y_640_, sizeof(void*)*3 + 3);
v_options_688_ = lean_ctor_get(v_toCold_686_, 2);
v___x_689_ = 1;
v___x_690_ = 0;
if (v_isRecordingDeps_687_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_Lean_Elab_async;
lean_inc_ref(v_options_688_);
v___x_692_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_options_688_, v___x_691_, v_isRecordingDeps_687_);
v___y_615_ = v___x_665_;
v___y_616_ = v___y_634_;
v___y_617_ = v___y_640_;
v___y_618_ = v___x_690_;
v___y_619_ = v___y_641_;
v___y_620_ = v___x_689_;
v___y_621_ = v___x_650_;
v___y_622_ = v___y_638_;
v___y_623_ = v___y_639_;
v___y_624_ = v___x_692_;
goto v___jp_614_;
}
else
{
lean_object* v___x_693_; 
lean_inc_ref(v_options_688_);
v___x_693_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_688_);
v___y_615_ = v___x_665_;
v___y_616_ = v___y_634_;
v___y_617_ = v___y_640_;
v___y_618_ = v___x_690_;
v___y_619_ = v___y_641_;
v___y_620_ = v___x_689_;
v___y_621_ = v___x_650_;
v___y_622_ = v___y_638_;
v___y_623_ = v___y_639_;
v___y_624_ = v___x_693_;
goto v___jp_614_;
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref_known(v___x_650_, 1);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_634_);
v_a_694_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_685_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_685_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
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
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
v_a_708_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_644_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_644_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v_checkType_271_);
v_a_716_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_642_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_642_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_725_; lean_object* v_env_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_725_ = lean_st_ref_get(v___y_277_);
v_env_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_728_ = l_Lean_Core_mkFreshUserName(v___x_727_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l_Lean_mkPrivateName(v_env_726_, v_a_729_);
lean_dec_ref(v_env_726_);
v___x_731_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_273_, v___y_275_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_params_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_n(v_a_732_, 2);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_734_ = l_Lean_collectLevelParams(v___x_733_, v_a_732_);
v_params_735_ = lean_ctor_get(v___x_734_, 2);
lean_inc_ref(v_params_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = l_Lean_Expr_hasMVar(v_a_732_);
if (v___x_737_ == 0)
{
v___y_634_ = v___x_730_;
v___y_635_ = v_a_732_;
v___y_636_ = v___x_736_;
v___y_637_ = v_params_735_;
v___y_638_ = v___y_274_;
v___y_639_ = v___y_275_;
v___y_640_ = v___y_276_;
v___y_641_ = v___y_277_;
goto v___jp_633_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_732_);
v___x_739_ = l_Lean_indentExpr(v_a_732_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_740_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_dec_ref_known(v___x_741_, 1);
v___y_634_ = v___x_730_;
v___y_635_ = v_a_732_;
v___y_636_ = v___x_736_;
v___y_637_ = v_params_735_;
v___y_638_ = v___y_274_;
v___y_639_ = v___y_275_;
v___y_640_ = v___y_276_;
v___y_641_ = v___y_277_;
goto v___jp_633_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_params_735_);
lean_dec(v_a_732_);
lean_dec(v___x_730_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec_ref(v_checkType_271_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v___x_730_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec_ref(v_checkType_271_);
v_a_750_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_731_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_731_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_env_726_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec_ref(v_value_273_);
lean_dec_ref(v_checkType_271_);
v_a_758_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_728_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_728_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_766_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_mctx_780_; lean_object* v_zetaDeltaFVarIds_781_; lean_object* v_postponed_782_; lean_object* v_diag_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_792_; 
v___x_776_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_777_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_777_, 0, v___y_775_);
lean_ctor_set(v___x_777_, 1, v_nextMacroScope_767_);
lean_ctor_set(v___x_777_, 2, v_ngen_768_);
lean_ctor_set(v___x_777_, 3, v_auxDeclNGen_769_);
lean_ctor_set(v___x_777_, 4, v_traceState_770_);
lean_ctor_set(v___x_777_, 5, v___x_776_);
lean_ctor_set(v___x_777_, 6, v_recordedDeps_771_);
lean_ctor_set(v___x_777_, 7, v_messages_772_);
lean_ctor_set(v___x_777_, 8, v_infoState_773_);
lean_ctor_set(v___x_777_, 9, v_snapshotTasks_774_);
v___x_778_ = lean_st_ref_put(v___y_277_, v___x_777_);
v___x_779_ = lean_st_ref_take(v___y_275_);
v_mctx_780_ = lean_ctor_get(v___x_779_, 0);
v_zetaDeltaFVarIds_781_ = lean_ctor_get(v___x_779_, 2);
v_postponed_782_ = lean_ctor_get(v___x_779_, 3);
v_diag_783_ = lean_ctor_get(v___x_779_, 4);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_779_, 1);
lean_dec(v_unused_793_);
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_diag_783_);
lean_inc(v_postponed_782_);
lean_inc(v_zetaDeltaFVarIds_781_);
lean_inc(v_mctx_780_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_mctx_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_zetaDeltaFVarIds_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_postponed_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_diag_783_);
v___x_789_ = v_reuseFailAlloc_791_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; 
v___x_790_ = lean_st_ref_put(v___y_275_, v___x_789_);
goto v___jp_724_;
}
}
}
v___jp_795_:
{
lean_object* v___x_796_; lean_object* v_env_797_; lean_object* v_nextMacroScope_798_; lean_object* v_ngen_799_; lean_object* v_auxDeclNGen_800_; lean_object* v_traceState_801_; lean_object* v_recordedDeps_802_; lean_object* v_messages_803_; lean_object* v_infoState_804_; lean_object* v_snapshotTasks_805_; lean_object* v___x_806_; 
v___x_796_ = lean_st_ref_take(v___y_277_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref_n(v_env_797_, 2);
v_nextMacroScope_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc(v_nextMacroScope_798_);
v_ngen_799_ = lean_ctor_get(v___x_796_, 2);
lean_inc_ref(v_ngen_799_);
v_auxDeclNGen_800_ = lean_ctor_get(v___x_796_, 3);
lean_inc_ref(v_auxDeclNGen_800_);
v_traceState_801_ = lean_ctor_get(v___x_796_, 4);
lean_inc_ref(v_traceState_801_);
v_recordedDeps_802_ = lean_ctor_get(v___x_796_, 6);
lean_inc_ref(v_recordedDeps_802_);
v_messages_803_ = lean_ctor_get(v___x_796_, 7);
lean_inc_ref(v_messages_803_);
v_infoState_804_ = lean_ctor_get(v___x_796_, 8);
lean_inc_ref(v_infoState_804_);
v_snapshotTasks_805_ = lean_ctor_get(v___x_796_, 9);
lean_inc_ref(v_snapshotTasks_805_);
lean_dec(v___x_796_);
v___x_806_ = l_Lean_Environment_importEnv_x3f(v_env_797_);
if (lean_obj_tag(v___x_806_) == 0)
{
v_nextMacroScope_767_ = v_nextMacroScope_798_;
v_ngen_768_ = v_ngen_799_;
v_auxDeclNGen_769_ = v_auxDeclNGen_800_;
v_traceState_770_ = v_traceState_801_;
v_recordedDeps_771_ = v_recordedDeps_802_;
v_messages_772_ = v_messages_803_;
v_infoState_773_ = v_infoState_804_;
v_snapshotTasks_774_ = v_snapshotTasks_805_;
v___y_775_ = v_env_797_;
goto v___jp_766_;
}
else
{
lean_object* v_val_807_; 
lean_dec_ref(v_env_797_);
v_val_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_806_, 1);
v_nextMacroScope_767_ = v_nextMacroScope_798_;
v_ngen_768_ = v_ngen_799_;
v_auxDeclNGen_769_ = v_auxDeclNGen_800_;
v_traceState_770_ = v_traceState_801_;
v_recordedDeps_771_ = v_recordedDeps_802_;
v_messages_772_ = v_messages_803_;
v_infoState_773_ = v_infoState_804_;
v_snapshotTasks_774_ = v_snapshotTasks_805_;
v___y_775_ = v_val_807_;
goto v___jp_766_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_evalExprCore___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_checkMeta_270_ = stack[0].m_num;
lean_object* v_checkType_271_ = stack[1].m_obj;
uint8_t v_safety_272_ = stack[2].m_num;
lean_object* v_value_273_ = stack[3].m_obj;
lean_object* v___y_274_ = stack[4].m_obj;
lean_object* v___y_275_ = stack[5].m_obj;
lean_object* v___y_276_ = stack[6].m_obj;
lean_object* v___y_277_ = stack[7].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_270_, v_checkType_271_, v_safety_272_, v_value_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_817_, lean_object* v_checkType_818_, lean_object* v_safety_819_, lean_object* v_value_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_checkMeta_boxed_826_; uint8_t v_safety_boxed_827_; lean_object* v_res_828_; 
v_checkMeta_boxed_826_ = lean_unbox(v_checkMeta_817_);
v_safety_boxed_827_ = lean_unbox(v_safety_819_);
v_res_828_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_826_, v_checkType_818_, v_safety_boxed_827_, v_value_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v_res_828_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object* v_env_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_traceState_837_; lean_object* v_recordedDeps_838_; lean_object* v_messages_839_; lean_object* v_infoState_840_; lean_object* v_snapshotTasks_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
v___x_833_ = lean_st_ref_take(v___y_831_);
v_nextMacroScope_834_ = lean_ctor_get(v___x_833_, 1);
v_ngen_835_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_836_ = lean_ctor_get(v___x_833_, 3);
v_traceState_837_ = lean_ctor_get(v___x_833_, 4);
v_recordedDeps_838_ = lean_ctor_get(v___x_833_, 6);
v_messages_839_ = lean_ctor_get(v___x_833_, 7);
v_infoState_840_ = lean_ctor_get(v___x_833_, 8);
v_snapshotTasks_841_ = lean_ctor_get(v___x_833_, 9);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v___x_833_, 5);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_869_);
v___x_843_ = v___x_833_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snapshotTasks_841_);
lean_inc(v_infoState_840_);
lean_inc(v_messages_839_);
lean_inc(v_recordedDeps_838_);
lean_inc(v_traceState_837_);
lean_inc(v_auxDeclNGen_836_);
lean_inc(v_ngen_835_);
lean_inc(v_nextMacroScope_834_);
lean_dec(v___x_833_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 5, v___x_845_);
lean_ctor_set(v___x_843_, 0, v_env_829_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_env_829_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_traceState_837_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_866_, 6, v_recordedDeps_838_);
lean_ctor_set(v_reuseFailAlloc_866_, 7, v_messages_839_);
lean_ctor_set(v_reuseFailAlloc_866_, 8, v_infoState_840_);
lean_ctor_set(v_reuseFailAlloc_866_, 9, v_snapshotTasks_841_);
v___x_847_ = v_reuseFailAlloc_866_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_mctx_850_; lean_object* v_zetaDeltaFVarIds_851_; lean_object* v_postponed_852_; lean_object* v_diag_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
v___x_848_ = lean_st_ref_put(v___y_831_, v___x_847_);
v___x_849_ = lean_st_ref_take(v___y_830_);
v_mctx_850_ = lean_ctor_get(v___x_849_, 0);
v_zetaDeltaFVarIds_851_ = lean_ctor_get(v___x_849_, 2);
v_postponed_852_ = lean_ctor_get(v___x_849_, 3);
v_diag_853_ = lean_ctor_get(v___x_849_, 4);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v___x_849_, 1);
lean_dec(v_unused_865_);
v___x_855_ = v___x_849_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_diag_853_);
lean_inc(v_postponed_852_);
lean_inc(v_zetaDeltaFVarIds_851_);
lean_inc(v_mctx_850_);
lean_dec(v___x_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_mctx_850_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_zetaDeltaFVarIds_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_postponed_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_diag_853_);
v___x_860_ = v_reuseFailAlloc_863_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_st_ref_put(v___y_830_, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_857_);
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_829_ = stack[0].m_obj;
lean_object* v___y_830_ = stack[1].m_obj;
lean_object* v___y_831_ = stack[2].m_obj;
lean_object* v_res_870_;
v_res_870_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_829_, v___y_830_, v___y_831_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object* v_env_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec(v___y_872_);
return v_res_875_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object* v_env_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_env_884_; lean_object* v_a_886_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_883_ = lean_st_ref_get(v___y_881_);
v_env_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_env_884_);
lean_dec(v___x_883_);
v___x_896_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_876_, v___y_879_, v___y_881_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
v___x_897_ = lean_apply_5(v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, lean_box(0));
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_884_, v___y_879_, v___y_881_);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_907_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_a_898_);
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_a_908_; 
v_a_908_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_897_, 1);
v_a_886_ = v_a_908_;
goto v___jp_885_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v___x_887_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_884_, v___y_879_, v___y_881_);
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
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v_a_886_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_876_ = stack[0].m_obj;
lean_object* v_x_877_ = stack[1].m_obj;
lean_object* v___y_878_ = stack[2].m_obj;
lean_object* v___y_879_ = stack[3].m_obj;
lean_object* v___y_880_ = stack[4].m_obj;
lean_object* v___y_881_ = stack[5].m_obj;
lean_object* v_res_909_;
v_res_909_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object* v_env_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_910_, v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_918_, lean_object* v_checkType_919_, uint8_t v_safety_920_, uint8_t v_checkMeta_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v_env_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = lean_box(v_checkMeta_921_);
v___x_928_ = lean_box(v_safety_920_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_929_, 0, v___x_927_);
lean_closure_set(v___f_929_, 1, v_checkType_919_);
lean_closure_set(v___f_929_, 2, v___x_928_);
lean_closure_set(v___f_929_, 3, v_value_918_);
v___x_930_ = lean_st_ref_get(v_a_925_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_env_931_);
lean_dec(v___x_930_);
v___x_932_ = l_Lean_Environment_unlockAsync(v_env_931_);
v___x_933_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v___x_932_, v___f_929_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_933_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExprCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_918_ = stack[0].m_obj;
lean_object* v_checkType_919_ = stack[1].m_obj;
uint8_t v_safety_920_ = stack[2].m_num;
uint8_t v_checkMeta_921_ = stack[3].m_num;
lean_object* v_a_922_ = stack[4].m_obj;
lean_object* v_a_923_ = stack[5].m_obj;
lean_object* v_a_924_ = stack[6].m_obj;
lean_object* v_a_925_ = stack[7].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Meta_evalExprCore___redArg(v_value_918_, v_checkType_919_, v_safety_920_, v_checkMeta_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_935_, lean_object* v_checkType_936_, lean_object* v_safety_937_, lean_object* v_checkMeta_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_safety_boxed_944_; uint8_t v_checkMeta_boxed_945_; lean_object* v_res_946_; 
v_safety_boxed_944_ = lean_unbox(v_safety_937_);
v_checkMeta_boxed_945_ = lean_unbox(v_checkMeta_938_);
v_res_946_ = l_Lean_Meta_evalExprCore___redArg(v_value_935_, v_checkType_936_, v_safety_boxed_944_, v_checkMeta_boxed_945_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_946_;
}
}
lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_947_, lean_object* v_value_948_, lean_object* v_checkType_949_, uint8_t v_safety_950_, uint8_t v_checkMeta_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Meta_evalExprCore___redArg(v_value_948_, v_checkType_949_, v_safety_950_, v_checkMeta_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
return v___x_957_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExprCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_948_ = stack[1].m_obj;
lean_object* v_checkType_949_ = stack[2].m_obj;
uint8_t v_safety_950_ = stack[3].m_num;
uint8_t v_checkMeta_951_ = stack[4].m_num;
lean_object* v_a_952_ = stack[5].m_obj;
lean_object* v_a_953_ = stack[6].m_obj;
lean_object* v_a_954_ = stack[7].m_obj;
lean_object* v_a_955_ = stack[8].m_obj;
lean_object* v_res_958_;
v_res_958_ = l_Lean_Meta_evalExprCore(lean_box(0), v_value_948_, v_checkType_949_, v_safety_950_, v_checkMeta_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_959_, lean_object* v_value_960_, lean_object* v_checkType_961_, lean_object* v_safety_962_, lean_object* v_checkMeta_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
uint8_t v_safety_boxed_969_; uint8_t v_checkMeta_boxed_970_; lean_object* v_res_971_; 
v_safety_boxed_969_ = lean_unbox(v_safety_962_);
v_checkMeta_boxed_970_ = lean_unbox(v_checkMeta_963_);
v_res_971_ = l_Lean_Meta_evalExprCore(v_00_u03b1_959_, v_value_960_, v_checkType_961_, v_safety_boxed_969_, v_checkMeta_boxed_970_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_971_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_object* v_00_u03b1_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v___x_978_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_973_ = stack[1].m_obj;
lean_object* v___y_974_ = stack[2].m_obj;
lean_object* v___y_975_ = stack[3].m_obj;
lean_object* v___y_976_ = stack[4].m_obj;
lean_object* v_res_979_;
v_res_979_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_box(0), v___y_973_, v___y_974_, v___y_975_, v___y_976_);
stack->m_obj
 = v_res_979_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___boxed(lean_object* v_00_u03b1_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(v_00_u03b1_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_986_;
}
}
lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_00_u03b1_987_, lean_object* v_constName_988_, uint8_t v_checkMeta_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_988_, v_checkMeta_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_988_ = stack[1].m_obj;
uint8_t v_checkMeta_989_ = stack[2].m_num;
lean_object* v___y_990_ = stack[3].m_obj;
lean_object* v___y_991_ = stack[4].m_obj;
lean_object* v___y_992_ = stack[5].m_obj;
lean_object* v___y_993_ = stack[6].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_box(0), v_constName_988_, v_checkMeta_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_00_u03b1_997_, lean_object* v_constName_998_, lean_object* v_checkMeta_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_checkMeta_boxed_1005_; lean_object* v_res_1006_; 
v_checkMeta_boxed_1005_ = lean_unbox(v_checkMeta_999_);
v_res_1006_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(v_00_u03b1_997_, v_constName_998_, v_checkMeta_boxed_1005_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1006_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1008_ = stack[1].m_obj;
lean_object* v___y_1009_ = stack[2].m_obj;
lean_object* v___y_1010_ = stack[3].m_obj;
lean_object* v___y_1011_ = stack[4].m_obj;
lean_object* v___y_1012_ = stack[5].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_box(0), v_msg_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_1016_, v_msg_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object* v_env_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_1024_, v___y_1026_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1024_ = stack[0].m_obj;
lean_object* v___y_1025_ = stack[1].m_obj;
lean_object* v___y_1026_ = stack[2].m_obj;
lean_object* v___y_1027_ = stack[3].m_obj;
lean_object* v___y_1028_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object* v_env_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v_00_u03b1_1039_, lean_object* v_env_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_1040_, v_x_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1040_ = stack[1].m_obj;
lean_object* v_x_1041_ = stack[2].m_obj;
lean_object* v___y_1042_ = stack[3].m_obj;
lean_object* v___y_1043_ = stack[4].m_obj;
lean_object* v___y_1044_ = stack[5].m_obj;
lean_object* v___y_1045_ = stack[6].m_obj;
lean_object* v_res_1048_;
v_res_1048_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_box(0), v_env_1040_, v_x_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_env_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(v_00_u03b1_1049_, v_env_1050_, v_x_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1057_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_object* v_00_u03b1_1058_, lean_object* v_x_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1059_ = stack[1].m_obj;
lean_object* v___y_1060_ = stack[2].m_obj;
lean_object* v___y_1061_ = stack[3].m_obj;
lean_object* v___y_1062_ = stack[4].m_obj;
lean_object* v___y_1063_ = stack[5].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_box(0), v_x_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(v_00_u03b1_1067_, v_x_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1078_, lean_object* v_type_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_whnfD(v_type_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lean_Expr_isConstOf(v_a_1086_, v_typeName_1078_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1088_);
v___x_1091_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1092_ = l_Lean_indentExpr(v_a_1086_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1093_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
lean_dec(v_a_1086_);
v___x_1095_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1095_);
v___x_1097_ = v___x_1088_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1085_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1085_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
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
}
LEAN_EXPORT void l_Lean_Meta_evalExpr_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1078_ = stack[0].m_obj;
lean_object* v_type_1079_ = stack[1].m_obj;
lean_object* v___y_1080_ = stack[2].m_obj;
lean_object* v___y_1081_ = stack[3].m_obj;
lean_object* v___y_1082_ = stack[4].m_obj;
lean_object* v___y_1083_ = stack[5].m_obj;
lean_object* v_res_1108_;
v_res_1108_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1078_, v_type_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
stack->m_obj
 = v_res_1108_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1109_, lean_object* v_type_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1109_, v_type_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v_typeName_1109_);
return v_res_1116_;
}
}
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1117_, lean_object* v_value_1118_, uint8_t v_safety_1119_, uint8_t v_checkMeta_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___f_1126_; lean_object* v___x_1127_; 
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1126_, 0, v_typeName_1117_);
v___x_1127_ = l_Lean_Meta_evalExprCore___redArg(v_value_1118_, v___f_1126_, v_safety_1119_, v_checkMeta_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExpr_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1117_ = stack[0].m_obj;
lean_object* v_value_1118_ = stack[1].m_obj;
uint8_t v_safety_1119_ = stack[2].m_num;
uint8_t v_checkMeta_1120_ = stack[3].m_num;
lean_object* v_a_1121_ = stack[4].m_obj;
lean_object* v_a_1122_ = stack[5].m_obj;
lean_object* v_a_1123_ = stack[6].m_obj;
lean_object* v_a_1124_ = stack[7].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1117_, v_value_1118_, v_safety_1119_, v_checkMeta_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1129_, lean_object* v_value_1130_, lean_object* v_safety_1131_, lean_object* v_checkMeta_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
uint8_t v_safety_boxed_1138_; uint8_t v_checkMeta_boxed_1139_; lean_object* v_res_1140_; 
v_safety_boxed_1138_ = lean_unbox(v_safety_1131_);
v_checkMeta_boxed_1139_ = lean_unbox(v_checkMeta_1132_);
v_res_1140_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1129_, v_value_1130_, v_safety_boxed_1138_, v_checkMeta_boxed_1139_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
return v_res_1140_;
}
}
lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1141_, lean_object* v_typeName_1142_, lean_object* v_value_1143_, uint8_t v_safety_1144_, uint8_t v_checkMeta_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1142_, v_value_1143_, v_safety_1144_, v_checkMeta_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExpr_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1142_ = stack[1].m_obj;
lean_object* v_value_1143_ = stack[2].m_obj;
uint8_t v_safety_1144_ = stack[3].m_num;
uint8_t v_checkMeta_1145_ = stack[4].m_num;
lean_object* v_a_1146_ = stack[5].m_obj;
lean_object* v_a_1147_ = stack[6].m_obj;
lean_object* v_a_1148_ = stack[7].m_obj;
lean_object* v_a_1149_ = stack[8].m_obj;
lean_object* v_res_1152_;
v_res_1152_ = l_Lean_Meta_evalExpr_x27(lean_box(0), v_typeName_1142_, v_value_1143_, v_safety_1144_, v_checkMeta_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
stack->m_obj
 = v_res_1152_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_typeName_1154_, lean_object* v_value_1155_, lean_object* v_safety_1156_, lean_object* v_checkMeta_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v_safety_boxed_1163_; uint8_t v_checkMeta_boxed_1164_; lean_object* v_res_1165_; 
v_safety_boxed_1163_ = lean_unbox(v_safety_1156_);
v_checkMeta_boxed_1164_ = lean_unbox(v_checkMeta_1157_);
v_res_1165_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1153_, v_typeName_1154_, v_value_1155_, v_safety_boxed_1163_, v_checkMeta_boxed_1164_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1171_, lean_object* v_type_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
lean_inc_ref(v_expectedType_1171_);
lean_inc_ref(v_type_1172_);
v___x_1178_ = l_Lean_Meta_isExprDefEq(v_type_1172_, v_expectedType_1171_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1203_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_unbox(v_a_1179_);
lean_dec(v_a_1179_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_del_object(v___x_1181_);
v___x_1184_ = lean_box(0);
v___x_1185_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1186_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1172_, v_expectedType_1171_, v___x_1184_, v___x_1185_, v___y_1173_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v_a_1187_);
v___x_1190_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1189_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1190_;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1186_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1186_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec_ref(v_type_1172_);
lean_dec_ref(v_expectedType_1171_);
v___x_1199_ = lean_box(0);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1199_);
v___x_1201_ = v___x_1181_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_type_1172_);
lean_dec_ref(v_expectedType_1171_);
v_a_1204_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1178_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1178_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_evalExpr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_1171_ = stack[0].m_obj;
lean_object* v_type_1172_ = stack[1].m_obj;
lean_object* v___y_1173_ = stack[2].m_obj;
lean_object* v___y_1174_ = stack[3].m_obj;
lean_object* v___y_1175_ = stack[4].m_obj;
lean_object* v___y_1176_ = stack[5].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1171_, v_type_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1213_, lean_object* v_type_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1213_, v_type_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1221_, lean_object* v_value_1222_, uint8_t v_safety_1223_, uint8_t v_checkMeta_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___f_1230_; lean_object* v___x_1231_; 
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1230_, 0, v_expectedType_1221_);
v___x_1231_ = l_Lean_Meta_evalExprCore___redArg(v_value_1222_, v___f_1230_, v_safety_1223_, v_checkMeta_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_1221_ = stack[0].m_obj;
lean_object* v_value_1222_ = stack[1].m_obj;
uint8_t v_safety_1223_ = stack[2].m_num;
uint8_t v_checkMeta_1224_ = stack[3].m_num;
lean_object* v_a_1225_ = stack[4].m_obj;
lean_object* v_a_1226_ = stack[5].m_obj;
lean_object* v_a_1227_ = stack[6].m_obj;
lean_object* v_a_1228_ = stack[7].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1221_, v_value_1222_, v_safety_1223_, v_checkMeta_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1233_, lean_object* v_value_1234_, lean_object* v_safety_1235_, lean_object* v_checkMeta_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_safety_boxed_1242_; uint8_t v_checkMeta_boxed_1243_; lean_object* v_res_1244_; 
v_safety_boxed_1242_ = lean_unbox(v_safety_1235_);
v_checkMeta_boxed_1243_ = lean_unbox(v_checkMeta_1236_);
v_res_1244_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1233_, v_value_1234_, v_safety_boxed_1242_, v_checkMeta_boxed_1243_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
return v_res_1244_;
}
}
lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1245_, lean_object* v_expectedType_1246_, lean_object* v_value_1247_, uint8_t v_safety_1248_, uint8_t v_checkMeta_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1246_, v_value_1247_, v_safety_1248_, v_checkMeta_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT void l_Lean_Meta_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_1246_ = stack[1].m_obj;
lean_object* v_value_1247_ = stack[2].m_obj;
uint8_t v_safety_1248_ = stack[3].m_num;
uint8_t v_checkMeta_1249_ = stack[4].m_num;
lean_object* v_a_1250_ = stack[5].m_obj;
lean_object* v_a_1251_ = stack[6].m_obj;
lean_object* v_a_1252_ = stack[7].m_obj;
lean_object* v_a_1253_ = stack[8].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l_Lean_Meta_evalExpr(lean_box(0), v_expectedType_1246_, v_value_1247_, v_safety_1248_, v_checkMeta_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_expectedType_1258_, lean_object* v_value_1259_, lean_object* v_safety_1260_, lean_object* v_checkMeta_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
uint8_t v_safety_boxed_1267_; uint8_t v_checkMeta_boxed_1268_; lean_object* v_res_1269_; 
v_safety_boxed_1267_ = lean_unbox(v_safety_1260_);
v_checkMeta_boxed_1268_ = lean_unbox(v_checkMeta_1261_);
v_res_1269_ = l_Lean_Meta_evalExpr(v_00_u03b1_1257_, v_expectedType_1258_, v_value_1259_, v_safety_boxed_1267_, v_checkMeta_boxed_1268_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1269_;
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

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
v___x_241_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set(v___x_241_, 4, v___x_240_);
lean_ctor_set(v___x_241_, 5, v___x_240_);
lean_ctor_set(v___x_241_, 6, v___x_240_);
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
uint8_t v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; uint16_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; uint16_t v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; uint8_t v___y_333_; uint8_t v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; uint16_t v___y_365_; uint8_t v___y_366_; lean_object* v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; uint8_t v___y_372_; uint8_t v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; uint8_t v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint16_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; uint8_t v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_448_; uint8_t v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; uint16_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint16_t v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; uint8_t v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; uint16_t v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; uint16_t v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; uint8_t v___y_597_; lean_object* v___y_598_; uint8_t v___y_599_; lean_object* v___y_600_; uint16_t v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; uint8_t v___y_606_; uint8_t v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; uint8_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v_nextMacroScope_760_; lean_object* v_ngen_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_traceState_763_; lean_object* v_recordedDeps_764_; lean_object* v_messages_765_; lean_object* v_infoState_766_; lean_object* v_snapshotTasks_767_; lean_object* v___y_768_; lean_object* v___x_787_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_787_ = lean_st_ref_get(v___y_267_);
lean_inc_ref(v_value_263_);
v___x_801_ = l_Lean_Expr_getUsedConstants(v_value_263_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v___x_801_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec_ref(v___x_801_);
lean_dec(v___x_787_);
goto v___jp_788_;
}
else
{
if (v___x_804_ == 0)
{
lean_dec_ref(v___x_801_);
lean_dec(v___x_787_);
goto v___jp_788_;
}
else
{
lean_object* v_env_805_; size_t v___x_806_; size_t v___x_807_; uint8_t v___x_808_; 
v_env_805_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_787_);
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_803_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v_env_805_, v___x_803_, v___x_801_, v___x_806_, v___x_807_);
lean_dec_ref(v___x_801_);
lean_dec_ref(v_env_805_);
if (v___x_808_ == 0)
{
goto v___jp_788_;
}
else
{
goto v___jp_717_;
}
}
}
v___jp_269_:
{
lean_object* v_toCold_281_; lean_object* v_currRecDepth_282_; lean_object* v_ref_283_; uint8_t v_suppressElabErrors_284_; uint8_t v_checkDeprecated_285_; uint8_t v_isRecordingDeps_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_323_; 
v_toCold_281_ = lean_ctor_get(v___y_279_, 0);
v_currRecDepth_282_ = lean_ctor_get(v___y_279_, 1);
v_ref_283_ = lean_ctor_get(v___y_279_, 2);
v_suppressElabErrors_284_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 2);
v_checkDeprecated_285_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 3);
v_isRecordingDeps_286_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 4);
v_isSharedCheck_323_ = !lean_is_exclusive(v___y_279_);
if (v_isSharedCheck_323_ == 0)
{
v___x_288_ = v___y_279_;
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_ref_283_);
lean_inc(v_currRecDepth_282_);
lean_inc(v_toCold_281_);
lean_dec(v___y_279_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_fileName_290_; lean_object* v_fileMap_291_; lean_object* v_currNamespace_292_; lean_object* v_openDecls_293_; lean_object* v_initHeartbeats_294_; lean_object* v_maxHeartbeats_295_; lean_object* v_quotContext_296_; lean_object* v_currMacroScope_297_; lean_object* v_cancelTk_x3f_298_; lean_object* v_inheritedTraceOptions_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_320_; 
v_fileName_290_ = lean_ctor_get(v_toCold_281_, 0);
v_fileMap_291_ = lean_ctor_get(v_toCold_281_, 1);
v_currNamespace_292_ = lean_ctor_get(v_toCold_281_, 4);
v_openDecls_293_ = lean_ctor_get(v_toCold_281_, 5);
v_initHeartbeats_294_ = lean_ctor_get(v_toCold_281_, 6);
v_maxHeartbeats_295_ = lean_ctor_get(v_toCold_281_, 7);
v_quotContext_296_ = lean_ctor_get(v_toCold_281_, 8);
v_currMacroScope_297_ = lean_ctor_get(v_toCold_281_, 9);
v_cancelTk_x3f_298_ = lean_ctor_get(v_toCold_281_, 10);
v_inheritedTraceOptions_299_ = lean_ctor_get(v_toCold_281_, 11);
v_isSharedCheck_320_ = !lean_is_exclusive(v_toCold_281_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_321_ = lean_ctor_get(v_toCold_281_, 3);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_toCold_281_, 2);
lean_dec(v_unused_322_);
v___x_301_ = v_toCold_281_;
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_inheritedTraceOptions_299_);
lean_inc(v_cancelTk_x3f_298_);
lean_inc(v_currMacroScope_297_);
lean_inc(v_quotContext_296_);
lean_inc(v_maxHeartbeats_295_);
lean_inc(v_initHeartbeats_294_);
lean_inc(v_openDecls_293_);
lean_inc(v_currNamespace_292_);
lean_inc(v_fileMap_291_);
lean_inc(v_fileName_290_);
lean_dec(v_toCold_281_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_271_, v___y_276_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v___x_303_);
lean_ctor_set(v___x_301_, 2, v___y_271_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_fileName_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_fileMap_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v___y_271_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_currNamespace_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v_openDecls_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_initHeartbeats_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_maxHeartbeats_295_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_quotContext_296_);
lean_ctor_set(v_reuseFailAlloc_319_, 9, v_currMacroScope_297_);
lean_ctor_set(v_reuseFailAlloc_319_, 10, v_cancelTk_x3f_298_);
lean_ctor_set(v_reuseFailAlloc_319_, 11, v_inheritedTraceOptions_299_);
v___x_305_ = v_reuseFailAlloc_319_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_305_);
v___x_307_ = v___x_288_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_currRecDepth_282_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_ref_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*3 + 2, v_suppressElabErrors_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*3 + 3, v_checkDeprecated_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*3 + 4, v_isRecordingDeps_286_);
v___x_307_ = v_reuseFailAlloc_318_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
lean_ctor_set_uint16(v___x_307_, sizeof(void*)*3, v___y_274_);
v___x_308_ = l_Lean_addAndCompile(v___y_278_, v___y_275_, v___y_270_, v___x_307_, v___y_280_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v___y_273_, v_checkMeta_260_, v___y_277_, v___y_272_, v___x_307_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___x_307_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_277_);
return v___x_309_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___x_307_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_273_);
lean_dec(v___y_272_);
v_a_310_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
}
v___jp_324_:
{
lean_object* v___x_338_; lean_object* v_env_339_; lean_object* v_nextMacroScope_340_; lean_object* v_ngen_341_; lean_object* v_auxDeclNGen_342_; lean_object* v_traceState_343_; lean_object* v_recordedDeps_344_; lean_object* v_messages_345_; lean_object* v_infoState_346_; lean_object* v_snapshotTasks_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_356_; 
v___x_338_ = lean_st_ref_take(v___y_328_);
v_env_339_ = lean_ctor_get(v___x_338_, 0);
v_nextMacroScope_340_ = lean_ctor_get(v___x_338_, 1);
v_ngen_341_ = lean_ctor_get(v___x_338_, 2);
v_auxDeclNGen_342_ = lean_ctor_get(v___x_338_, 3);
v_traceState_343_ = lean_ctor_get(v___x_338_, 4);
v_recordedDeps_344_ = lean_ctor_get(v___x_338_, 6);
v_messages_345_ = lean_ctor_get(v___x_338_, 7);
v_infoState_346_ = lean_ctor_get(v___x_338_, 8);
v_snapshotTasks_347_ = lean_ctor_get(v___x_338_, 9);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v___x_338_, 5);
lean_dec(v_unused_357_);
v___x_349_ = v___x_338_;
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snapshotTasks_347_);
lean_inc(v_infoState_346_);
lean_inc(v_messages_345_);
lean_inc(v_recordedDeps_344_);
lean_inc(v_traceState_343_);
lean_inc(v_auxDeclNGen_342_);
lean_inc(v_ngen_341_);
lean_inc(v_nextMacroScope_340_);
lean_inc(v_env_339_);
lean_dec(v___x_338_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = l_Lean_Kernel_enableDiag(v_env_339_, v___y_333_);
lean_inc_ref(v___y_326_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 5, v___y_326_);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_nextMacroScope_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_ngen_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_auxDeclNGen_342_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_traceState_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v___y_326_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_recordedDeps_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_messages_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_infoState_346_);
lean_ctor_set(v_reuseFailAlloc_355_, 9, v_snapshotTasks_347_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_st_ref_put(v___y_328_, v___x_353_);
v___y_270_ = v___y_334_;
v___y_271_ = v___y_325_;
v___y_272_ = v___y_335_;
v___y_273_ = v___y_327_;
v___y_274_ = v___y_330_;
v___y_275_ = v___y_331_;
v___y_276_ = v___y_336_;
v___y_277_ = v___y_337_;
v___y_278_ = v___y_332_;
v___y_279_ = v___y_329_;
v___y_280_ = v___y_328_;
goto v___jp_269_;
}
}
}
v___jp_358_:
{
if (v___y_372_ == 0)
{
if (v___y_361_ == 0)
{
v___y_270_ = v___y_368_;
v___y_271_ = v___y_359_;
v___y_272_ = v___y_369_;
v___y_273_ = v___y_362_;
v___y_274_ = v___y_365_;
v___y_275_ = v___y_366_;
v___y_276_ = v___y_370_;
v___y_277_ = v___y_371_;
v___y_278_ = v___y_367_;
v___y_279_ = v___y_364_;
v___y_280_ = v___y_363_;
goto v___jp_269_;
}
else
{
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_362_;
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
v___y_330_ = v___y_365_;
v___y_331_ = v___y_366_;
v___y_332_ = v___y_367_;
v___y_333_ = v___y_372_;
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_371_;
goto v___jp_324_;
}
}
else
{
if (v___y_361_ == 0)
{
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_362_;
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
v___y_330_ = v___y_365_;
v___y_331_ = v___y_366_;
v___y_332_ = v___y_367_;
v___y_333_ = v___y_372_;
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_371_;
goto v___jp_324_;
}
else
{
v___y_270_ = v___y_368_;
v___y_271_ = v___y_359_;
v___y_272_ = v___y_369_;
v___y_273_ = v___y_362_;
v___y_274_ = v___y_365_;
v___y_275_ = v___y_366_;
v___y_276_ = v___y_370_;
v___y_277_ = v___y_371_;
v___y_278_ = v___y_367_;
v___y_279_ = v___y_364_;
v___y_280_ = v___y_363_;
goto v___jp_269_;
}
}
}
v___jp_373_:
{
uint16_t v___x_385_; lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v___x_388_; uint16_t v___x_389_; uint16_t v___x_390_; uint16_t v___x_391_; uint8_t v___x_392_; 
v___x_385_ = l_Lean_OptionFlags_ofOptions(v___y_384_);
v___x_386_ = lean_st_ref_get(v___y_379_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v___x_388_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_387_);
lean_dec_ref(v_env_387_);
v___x_389_ = 512;
v___x_390_ = lean_uint16_land(v___x_385_, v___x_389_);
v___x_391_ = 0;
v___x_392_ = lean_uint16_dec_eq(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
v___y_359_ = v___y_384_;
v___y_360_ = v___y_375_;
v___y_361_ = v___x_388_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_378_;
v___y_365_ = v___x_385_;
v___y_366_ = v___y_381_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_374_;
v___y_369_ = v___y_376_;
v___y_370_ = v___y_380_;
v___y_371_ = v___y_382_;
v___y_372_ = v___y_381_;
goto v___jp_358_;
}
else
{
v___y_359_ = v___y_384_;
v___y_360_ = v___y_375_;
v___y_361_ = v___x_388_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_378_;
v___y_365_ = v___x_385_;
v___y_366_ = v___y_381_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_374_;
v___y_369_ = v___y_376_;
v___y_370_ = v___y_380_;
v___y_371_ = v___y_382_;
v___y_372_ = v___y_374_;
goto v___jp_358_;
}
}
v___jp_393_:
{
lean_object* v_toCold_406_; lean_object* v_currRecDepth_407_; lean_object* v_ref_408_; uint8_t v_suppressElabErrors_409_; uint8_t v_checkDeprecated_410_; uint8_t v_isRecordingDeps_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_441_; 
v_toCold_406_ = lean_ctor_get(v___y_404_, 0);
v_currRecDepth_407_ = lean_ctor_get(v___y_404_, 1);
v_ref_408_ = lean_ctor_get(v___y_404_, 2);
v_suppressElabErrors_409_ = lean_ctor_get_uint8(v___y_404_, sizeof(void*)*3 + 2);
v_checkDeprecated_410_ = lean_ctor_get_uint8(v___y_404_, sizeof(void*)*3 + 3);
v_isRecordingDeps_411_ = lean_ctor_get_uint8(v___y_404_, sizeof(void*)*3 + 4);
v_isSharedCheck_441_ = !lean_is_exclusive(v___y_404_);
if (v_isSharedCheck_441_ == 0)
{
v___x_413_ = v___y_404_;
v_isShared_414_ = v_isSharedCheck_441_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_ref_408_);
lean_inc(v_currRecDepth_407_);
lean_inc(v_toCold_406_);
lean_dec(v___y_404_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_441_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_fileName_415_; lean_object* v_fileMap_416_; lean_object* v_currNamespace_417_; lean_object* v_openDecls_418_; lean_object* v_initHeartbeats_419_; lean_object* v_maxHeartbeats_420_; lean_object* v_quotContext_421_; lean_object* v_currMacroScope_422_; lean_object* v_cancelTk_x3f_423_; lean_object* v_inheritedTraceOptions_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_438_; 
v_fileName_415_ = lean_ctor_get(v_toCold_406_, 0);
v_fileMap_416_ = lean_ctor_get(v_toCold_406_, 1);
v_currNamespace_417_ = lean_ctor_get(v_toCold_406_, 4);
v_openDecls_418_ = lean_ctor_get(v_toCold_406_, 5);
v_initHeartbeats_419_ = lean_ctor_get(v_toCold_406_, 6);
v_maxHeartbeats_420_ = lean_ctor_get(v_toCold_406_, 7);
v_quotContext_421_ = lean_ctor_get(v_toCold_406_, 8);
v_currMacroScope_422_ = lean_ctor_get(v_toCold_406_, 9);
v_cancelTk_x3f_423_ = lean_ctor_get(v_toCold_406_, 10);
v_inheritedTraceOptions_424_ = lean_ctor_get(v_toCold_406_, 11);
v_isSharedCheck_438_ = !lean_is_exclusive(v_toCold_406_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; 
v_unused_439_ = lean_ctor_get(v_toCold_406_, 3);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_toCold_406_, 2);
lean_dec(v_unused_440_);
v___x_426_ = v_toCold_406_;
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_inheritedTraceOptions_424_);
lean_inc(v_cancelTk_x3f_423_);
lean_inc(v_currMacroScope_422_);
lean_inc(v_quotContext_421_);
lean_inc(v_maxHeartbeats_420_);
lean_inc(v_initHeartbeats_419_);
lean_inc(v_openDecls_418_);
lean_inc(v_currNamespace_417_);
lean_inc(v_fileMap_416_);
lean_inc(v_fileName_415_);
lean_dec(v_toCold_406_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_399_, v___y_401_);
lean_inc_ref(v___y_399_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 3, v___x_428_);
lean_ctor_set(v___x_426_, 2, v___y_399_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_fileName_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fileMap_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v___y_399_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_currNamespace_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_openDecls_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_initHeartbeats_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_maxHeartbeats_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_quotContext_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_currMacroScope_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_cancelTk_x3f_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_inheritedTraceOptions_424_);
v___x_430_ = v_reuseFailAlloc_437_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_430_);
v___x_432_ = v___x_413_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_currRecDepth_407_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ref_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3 + 2, v_suppressElabErrors_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3 + 3, v_checkDeprecated_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3 + 4, v_isRecordingDeps_411_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_ctor_set_uint16(v___x_432_, sizeof(void*)*3, v___y_398_);
if (v_isRecordingDeps_411_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_434_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_399_, v___x_433_, v___y_400_);
v___y_374_ = v___y_394_;
v___y_375_ = v___y_395_;
v___y_376_ = v___y_396_;
v___y_377_ = v___y_397_;
v___y_378_ = v___x_432_;
v___y_379_ = v___y_405_;
v___y_380_ = v___y_401_;
v___y_381_ = v___y_400_;
v___y_382_ = v___y_402_;
v___y_383_ = v___y_403_;
v___y_384_ = v___x_434_;
goto v___jp_373_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_399_);
v___y_374_ = v___y_394_;
v___y_375_ = v___y_395_;
v___y_376_ = v___y_396_;
v___y_377_ = v___y_397_;
v___y_378_ = v___x_432_;
v___y_379_ = v___y_405_;
v___y_380_ = v___y_401_;
v___y_381_ = v___y_400_;
v___y_382_ = v___y_402_;
v___y_383_ = v___y_403_;
v___y_384_ = v___x_435_;
goto v___jp_373_;
}
}
}
}
}
}
v___jp_442_:
{
lean_object* v___x_456_; lean_object* v_env_457_; lean_object* v_nextMacroScope_458_; lean_object* v_ngen_459_; lean_object* v_auxDeclNGen_460_; lean_object* v_traceState_461_; lean_object* v_recordedDeps_462_; lean_object* v_messages_463_; lean_object* v_infoState_464_; lean_object* v_snapshotTasks_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v___x_456_ = lean_st_ref_take(v___y_455_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
v_nextMacroScope_458_ = lean_ctor_get(v___x_456_, 1);
v_ngen_459_ = lean_ctor_get(v___x_456_, 2);
v_auxDeclNGen_460_ = lean_ctor_get(v___x_456_, 3);
v_traceState_461_ = lean_ctor_get(v___x_456_, 4);
v_recordedDeps_462_ = lean_ctor_get(v___x_456_, 6);
v_messages_463_ = lean_ctor_get(v___x_456_, 7);
v_infoState_464_ = lean_ctor_get(v___x_456_, 8);
v_snapshotTasks_465_ = lean_ctor_get(v___x_456_, 9);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_456_, 5);
lean_dec(v_unused_475_);
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snapshotTasks_465_);
lean_inc(v_infoState_464_);
lean_inc(v_messages_463_);
lean_inc(v_recordedDeps_462_);
lean_inc(v_traceState_461_);
lean_inc(v_auxDeclNGen_460_);
lean_inc(v_ngen_459_);
lean_inc(v_nextMacroScope_458_);
lean_inc(v_env_457_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = l_Lean_Kernel_enableDiag(v_env_457_, v___y_443_);
lean_inc_ref(v___y_444_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 5, v___y_444_);
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_nextMacroScope_458_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_ngen_459_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_auxDeclNGen_460_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_traceState_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 5, v___y_444_);
lean_ctor_set(v_reuseFailAlloc_473_, 6, v_recordedDeps_462_);
lean_ctor_set(v_reuseFailAlloc_473_, 7, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_473_, 8, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_473_, 9, v_snapshotTasks_465_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_st_ref_put(v___y_455_, v___x_471_);
v___y_394_ = v___y_449_;
v___y_395_ = v___y_444_;
v___y_396_ = v___y_450_;
v___y_397_ = v___y_445_;
v___y_398_ = v___y_452_;
v___y_399_ = v___y_446_;
v___y_400_ = v___y_447_;
v___y_401_ = v___y_453_;
v___y_402_ = v___y_454_;
v___y_403_ = v___y_448_;
v___y_404_ = v___y_451_;
v___y_405_ = v___y_455_;
goto v___jp_393_;
}
}
}
v___jp_476_:
{
if (v___y_490_ == 0)
{
if (v___y_478_ == 0)
{
v___y_394_ = v___y_483_;
v___y_395_ = v___y_477_;
v___y_396_ = v___y_484_;
v___y_397_ = v___y_479_;
v___y_398_ = v___y_486_;
v___y_399_ = v___y_480_;
v___y_400_ = v___y_481_;
v___y_401_ = v___y_487_;
v___y_402_ = v___y_488_;
v___y_403_ = v___y_482_;
v___y_404_ = v___y_485_;
v___y_405_ = v___y_489_;
goto v___jp_393_;
}
else
{
v___y_443_ = v___y_490_;
v___y_444_ = v___y_477_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_481_;
v___y_448_ = v___y_482_;
v___y_449_ = v___y_483_;
v___y_450_ = v___y_484_;
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
goto v___jp_442_;
}
}
else
{
if (v___y_478_ == 0)
{
v___y_443_ = v___y_490_;
v___y_444_ = v___y_477_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_481_;
v___y_448_ = v___y_482_;
v___y_449_ = v___y_483_;
v___y_450_ = v___y_484_;
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
goto v___jp_442_;
}
else
{
v___y_394_ = v___y_483_;
v___y_395_ = v___y_477_;
v___y_396_ = v___y_484_;
v___y_397_ = v___y_479_;
v___y_398_ = v___y_486_;
v___y_399_ = v___y_480_;
v___y_400_ = v___y_481_;
v___y_401_ = v___y_487_;
v___y_402_ = v___y_488_;
v___y_403_ = v___y_482_;
v___y_404_ = v___y_485_;
v___y_405_ = v___y_489_;
goto v___jp_393_;
}
}
}
v___jp_491_:
{
uint16_t v___x_503_; lean_object* v___x_504_; lean_object* v_env_505_; uint8_t v___x_506_; uint16_t v___x_507_; uint16_t v___x_508_; uint16_t v___x_509_; uint8_t v___x_510_; 
v___x_503_ = l_Lean_OptionFlags_ofOptions(v___y_502_);
v___x_504_ = lean_st_ref_get(v___y_500_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_env_505_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_505_);
lean_dec_ref(v_env_505_);
v___x_507_ = 512;
v___x_508_ = lean_uint16_land(v___x_503_, v___x_507_);
v___x_509_ = 0;
v___x_510_ = lean_uint16_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
v___y_477_ = v___y_493_;
v___y_478_ = v___x_506_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_502_;
v___y_481_ = v___y_498_;
v___y_482_ = v___y_501_;
v___y_483_ = v___y_492_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
v___y_486_ = v___x_503_;
v___y_487_ = v___y_497_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_498_;
goto v___jp_476_;
}
else
{
v___y_477_ = v___y_493_;
v___y_478_ = v___x_506_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_502_;
v___y_481_ = v___y_498_;
v___y_482_ = v___y_501_;
v___y_483_ = v___y_492_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
v___y_486_ = v___x_503_;
v___y_487_ = v___y_497_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_492_;
goto v___jp_476_;
}
}
v___jp_511_:
{
lean_object* v_toCold_523_; lean_object* v_currRecDepth_524_; lean_object* v_ref_525_; uint8_t v_suppressElabErrors_526_; uint8_t v_checkDeprecated_527_; uint8_t v_isRecordingDeps_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_559_; 
v_toCold_523_ = lean_ctor_get(v___y_521_, 0);
v_currRecDepth_524_ = lean_ctor_get(v___y_521_, 1);
v_ref_525_ = lean_ctor_get(v___y_521_, 2);
v_suppressElabErrors_526_ = lean_ctor_get_uint8(v___y_521_, sizeof(void*)*3 + 2);
v_checkDeprecated_527_ = lean_ctor_get_uint8(v___y_521_, sizeof(void*)*3 + 3);
v_isRecordingDeps_528_ = lean_ctor_get_uint8(v___y_521_, sizeof(void*)*3 + 4);
v_isSharedCheck_559_ = !lean_is_exclusive(v___y_521_);
if (v_isSharedCheck_559_ == 0)
{
v___x_530_ = v___y_521_;
v_isShared_531_ = v_isSharedCheck_559_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_ref_525_);
lean_inc(v_currRecDepth_524_);
lean_inc(v_toCold_523_);
lean_dec(v___y_521_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_559_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_fileName_532_; lean_object* v_fileMap_533_; lean_object* v_currNamespace_534_; lean_object* v_openDecls_535_; lean_object* v_initHeartbeats_536_; lean_object* v_maxHeartbeats_537_; lean_object* v_quotContext_538_; lean_object* v_currMacroScope_539_; lean_object* v_cancelTk_x3f_540_; lean_object* v_inheritedTraceOptions_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_556_; 
v_fileName_532_ = lean_ctor_get(v_toCold_523_, 0);
v_fileMap_533_ = lean_ctor_get(v_toCold_523_, 1);
v_currNamespace_534_ = lean_ctor_get(v_toCold_523_, 4);
v_openDecls_535_ = lean_ctor_get(v_toCold_523_, 5);
v_initHeartbeats_536_ = lean_ctor_get(v_toCold_523_, 6);
v_maxHeartbeats_537_ = lean_ctor_get(v_toCold_523_, 7);
v_quotContext_538_ = lean_ctor_get(v_toCold_523_, 8);
v_currMacroScope_539_ = lean_ctor_get(v_toCold_523_, 9);
v_cancelTk_x3f_540_ = lean_ctor_get(v_toCold_523_, 10);
v_inheritedTraceOptions_541_ = lean_ctor_get(v_toCold_523_, 11);
v_isSharedCheck_556_ = !lean_is_exclusive(v_toCold_523_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_557_ = lean_ctor_get(v_toCold_523_, 3);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_toCold_523_, 2);
lean_dec(v_unused_558_);
v___x_543_ = v_toCold_523_;
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_inheritedTraceOptions_541_);
lean_inc(v_cancelTk_x3f_540_);
lean_inc(v_currMacroScope_539_);
lean_inc(v_quotContext_538_);
lean_inc(v_maxHeartbeats_537_);
lean_inc(v_initHeartbeats_536_);
lean_inc(v_openDecls_535_);
lean_inc(v_currNamespace_534_);
lean_inc(v_fileMap_533_);
lean_inc(v_fileName_532_);
lean_dec(v_toCold_523_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = l_Lean_maxRecDepth;
v___x_546_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__1(v___y_514_, v___x_545_);
lean_inc_ref(v___y_514_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 3, v___x_546_);
lean_ctor_set(v___x_543_, 2, v___y_514_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_fileName_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_fileMap_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v___y_514_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_currNamespace_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_openDecls_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_initHeartbeats_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_maxHeartbeats_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_quotContext_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 9, v_currMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 10, v_cancelTk_x3f_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 11, v_inheritedTraceOptions_541_);
v___x_548_ = v_reuseFailAlloc_555_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_548_);
v___x_550_ = v___x_530_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_currRecDepth_524_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_ref_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*3 + 2, v_suppressElabErrors_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*3 + 3, v_checkDeprecated_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*3 + 4, v_isRecordingDeps_528_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_ctor_set_uint16(v___x_550_, sizeof(void*)*3, v___y_516_);
if (v_isRecordingDeps_528_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_552_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v___y_514_, v___x_551_, v_isRecordingDeps_528_);
v___y_492_ = v___y_512_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_515_;
v___y_495_ = v___x_550_;
v___y_496_ = v___y_517_;
v___y_497_ = v___x_545_;
v___y_498_ = v___y_518_;
v___y_499_ = v___y_519_;
v___y_500_ = v___y_522_;
v___y_501_ = v___y_520_;
v___y_502_ = v___x_552_;
goto v___jp_491_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_514_);
v___y_492_ = v___y_512_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_515_;
v___y_495_ = v___x_550_;
v___y_496_ = v___y_517_;
v___y_497_ = v___x_545_;
v___y_498_ = v___y_518_;
v___y_499_ = v___y_519_;
v___y_500_ = v___y_522_;
v___y_501_ = v___y_520_;
v___y_502_ = v___x_553_;
goto v___jp_491_;
}
}
}
}
}
}
v___jp_560_:
{
lean_object* v___x_573_; lean_object* v_env_574_; lean_object* v_nextMacroScope_575_; lean_object* v_ngen_576_; lean_object* v_auxDeclNGen_577_; lean_object* v_traceState_578_; lean_object* v_recordedDeps_579_; lean_object* v_messages_580_; lean_object* v_infoState_581_; lean_object* v_snapshotTasks_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v___x_573_ = lean_st_ref_take(v___y_570_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
v_nextMacroScope_575_ = lean_ctor_get(v___x_573_, 1);
v_ngen_576_ = lean_ctor_get(v___x_573_, 2);
v_auxDeclNGen_577_ = lean_ctor_get(v___x_573_, 3);
v_traceState_578_ = lean_ctor_get(v___x_573_, 4);
v_recordedDeps_579_ = lean_ctor_get(v___x_573_, 6);
v_messages_580_ = lean_ctor_get(v___x_573_, 7);
v_infoState_581_ = lean_ctor_get(v___x_573_, 8);
v_snapshotTasks_582_ = lean_ctor_get(v___x_573_, 9);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_573_, 5);
lean_dec(v_unused_592_);
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snapshotTasks_582_);
lean_inc(v_infoState_581_);
lean_inc(v_messages_580_);
lean_inc(v_recordedDeps_579_);
lean_inc(v_traceState_578_);
lean_inc(v_auxDeclNGen_577_);
lean_inc(v_ngen_576_);
lean_inc(v_nextMacroScope_575_);
lean_inc(v_env_574_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = l_Lean_Kernel_enableDiag(v_env_574_, v___y_563_);
lean_inc_ref(v___y_561_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 5, v___y_561_);
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_nextMacroScope_575_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_ngen_576_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_auxDeclNGen_577_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_traceState_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v___y_561_);
lean_ctor_set(v_reuseFailAlloc_590_, 6, v_recordedDeps_579_);
lean_ctor_set(v_reuseFailAlloc_590_, 7, v_messages_580_);
lean_ctor_set(v_reuseFailAlloc_590_, 8, v_infoState_581_);
lean_ctor_set(v_reuseFailAlloc_590_, 9, v_snapshotTasks_582_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_st_ref_put(v___y_570_, v___x_588_);
v___y_512_ = v___y_567_;
v___y_513_ = v___y_561_;
v___y_514_ = v___y_562_;
v___y_515_ = v___y_568_;
v___y_516_ = v___y_569_;
v___y_517_ = v___y_564_;
v___y_518_ = v___y_565_;
v___y_519_ = v___y_572_;
v___y_520_ = v___y_566_;
v___y_521_ = v___y_571_;
v___y_522_ = v___y_570_;
goto v___jp_511_;
}
}
}
v___jp_593_:
{
if (v___y_606_ == 0)
{
if (v___y_605_ == 0)
{
v___y_512_ = v___y_599_;
v___y_513_ = v___y_594_;
v___y_514_ = v___y_595_;
v___y_515_ = v___y_600_;
v___y_516_ = v___y_601_;
v___y_517_ = v___y_596_;
v___y_518_ = v___y_597_;
v___y_519_ = v___y_604_;
v___y_520_ = v___y_598_;
v___y_521_ = v___y_603_;
v___y_522_ = v___y_602_;
goto v___jp_511_;
}
else
{
v___y_561_ = v___y_594_;
v___y_562_ = v___y_595_;
v___y_563_ = v___y_606_;
v___y_564_ = v___y_596_;
v___y_565_ = v___y_597_;
v___y_566_ = v___y_598_;
v___y_567_ = v___y_599_;
v___y_568_ = v___y_600_;
v___y_569_ = v___y_601_;
v___y_570_ = v___y_602_;
v___y_571_ = v___y_603_;
v___y_572_ = v___y_604_;
goto v___jp_560_;
}
}
else
{
if (v___y_605_ == 0)
{
v___y_561_ = v___y_594_;
v___y_562_ = v___y_595_;
v___y_563_ = v___y_606_;
v___y_564_ = v___y_596_;
v___y_565_ = v___y_597_;
v___y_566_ = v___y_598_;
v___y_567_ = v___y_599_;
v___y_568_ = v___y_600_;
v___y_569_ = v___y_601_;
v___y_570_ = v___y_602_;
v___y_571_ = v___y_603_;
v___y_572_ = v___y_604_;
goto v___jp_560_;
}
else
{
v___y_512_ = v___y_599_;
v___y_513_ = v___y_594_;
v___y_514_ = v___y_595_;
v___y_515_ = v___y_600_;
v___y_516_ = v___y_601_;
v___y_517_ = v___y_596_;
v___y_518_ = v___y_597_;
v___y_519_ = v___y_604_;
v___y_520_ = v___y_598_;
v___y_521_ = v___y_603_;
v___y_522_ = v___y_602_;
goto v___jp_511_;
}
}
}
v___jp_607_:
{
uint16_t v___x_618_; lean_object* v___x_619_; lean_object* v_env_620_; uint8_t v___x_621_; uint16_t v___x_622_; uint16_t v___x_623_; uint16_t v___x_624_; uint8_t v___x_625_; 
v___x_618_ = l_Lean_OptionFlags_ofOptions(v___y_617_);
v___x_619_ = lean_st_ref_get(v___y_611_);
v_env_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_619_);
v___x_621_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_620_);
lean_dec_ref(v_env_620_);
v___x_622_ = 512;
v___x_623_ = lean_uint16_land(v___x_618_, v___x_622_);
v___x_624_ = 0;
v___x_625_ = lean_uint16_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_594_ = v___y_609_;
v___y_595_ = v___y_617_;
v___y_596_ = v___y_612_;
v___y_597_ = v___y_614_;
v___y_598_ = v___y_616_;
v___y_599_ = v___y_608_;
v___y_600_ = v___y_610_;
v___y_601_ = v___x_618_;
v___y_602_ = v___y_611_;
v___y_603_ = v___y_613_;
v___y_604_ = v___y_615_;
v___y_605_ = v___x_621_;
v___y_606_ = v___y_614_;
goto v___jp_593_;
}
else
{
v___y_594_ = v___y_609_;
v___y_595_ = v___y_617_;
v___y_596_ = v___y_612_;
v___y_597_ = v___y_614_;
v___y_598_ = v___y_616_;
v___y_599_ = v___y_608_;
v___y_600_ = v___y_610_;
v___y_601_ = v___x_618_;
v___y_602_ = v___y_611_;
v___y_603_ = v___y_613_;
v___y_604_ = v___y_615_;
v___y_605_ = v___x_621_;
v___y_606_ = v___y_608_;
goto v___jp_593_;
}
}
v___jp_626_:
{
lean_object* v___x_635_; 
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
lean_inc_ref(v___y_631_);
lean_inc_ref(v___y_630_);
v___x_635_ = lean_infer_type(v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_n(v_a_636_, 2);
lean_dec_ref_known(v___x_635_, 1);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
lean_inc_ref(v___y_631_);
v___x_637_ = lean_apply_6(v_checkType_261_, v_a_636_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, lean_box(0));
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_env_645_; lean_object* v_nextMacroScope_646_; lean_object* v_ngen_647_; lean_object* v_auxDeclNGen_648_; lean_object* v_traceState_649_; lean_object* v_recordedDeps_650_; lean_object* v_messages_651_; lean_object* v_infoState_652_; lean_object* v_snapshotTasks_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref_known(v___x_637_, 1);
v___x_638_ = lean_array_to_list(v___y_629_);
lean_inc_n(v___y_628_, 2);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v___y_628_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
lean_ctor_set(v___x_639_, 2, v_a_636_);
v___x_640_ = lean_box(0);
lean_inc(v___y_627_);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_628_);
lean_ctor_set(v___x_641_, 1, v___y_627_);
v___x_642_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___y_630_);
lean_ctor_set(v___x_642_, 2, v___x_640_);
lean_ctor_set(v___x_642_, 3, v___x_641_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*4, v_safety_262_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_st_ref_take(v___y_634_);
v_env_645_ = lean_ctor_get(v___x_644_, 0);
v_nextMacroScope_646_ = lean_ctor_get(v___x_644_, 1);
v_ngen_647_ = lean_ctor_get(v___x_644_, 2);
v_auxDeclNGen_648_ = lean_ctor_get(v___x_644_, 3);
v_traceState_649_ = lean_ctor_get(v___x_644_, 4);
v_recordedDeps_650_ = lean_ctor_get(v___x_644_, 6);
v_messages_651_ = lean_ctor_get(v___x_644_, 7);
v_infoState_652_ = lean_ctor_get(v___x_644_, 8);
v_snapshotTasks_653_ = lean_ctor_get(v___x_644_, 9);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_644_, 5);
lean_dec(v_unused_700_);
v___x_655_ = v___x_644_;
v_isShared_656_ = v_isSharedCheck_699_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snapshotTasks_653_);
lean_inc(v_infoState_652_);
lean_inc(v_messages_651_);
lean_inc(v_recordedDeps_650_);
lean_inc(v_traceState_649_);
lean_inc(v_auxDeclNGen_648_);
lean_inc(v_ngen_647_);
lean_inc(v_nextMacroScope_646_);
lean_inc(v_env_645_);
lean_dec(v___x_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_699_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
lean_inc(v___y_628_);
v___x_657_ = l_Lean_markMeta(v_env_645_, v___y_628_);
v___x_658_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 5, v___x_658_);
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_nextMacroScope_646_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_ngen_647_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_auxDeclNGen_648_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_traceState_649_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_recordedDeps_650_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_messages_651_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_infoState_652_);
lean_ctor_set(v_reuseFailAlloc_698_, 9, v_snapshotTasks_653_);
v___x_660_ = v_reuseFailAlloc_698_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_mctx_663_; lean_object* v_zetaDeltaFVarIds_664_; lean_object* v_postponed_665_; lean_object* v_diag_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_696_; 
v___x_661_ = lean_st_ref_put(v___y_634_, v___x_660_);
v___x_662_ = lean_st_ref_take(v___y_632_);
v_mctx_663_ = lean_ctor_get(v___x_662_, 0);
v_zetaDeltaFVarIds_664_ = lean_ctor_get(v___x_662_, 2);
v_postponed_665_ = lean_ctor_get(v___x_662_, 3);
v_diag_666_ = lean_ctor_get(v___x_662_, 4);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_697_);
v___x_668_ = v___x_662_;
v_isShared_669_ = v_isSharedCheck_696_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_diag_666_);
lean_inc(v_postponed_665_);
lean_inc(v_zetaDeltaFVarIds_664_);
lean_inc(v_mctx_663_);
lean_dec(v___x_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_696_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_mctx_663_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_zetaDeltaFVarIds_664_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_postponed_665_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_diag_666_);
v___x_672_ = v_reuseFailAlloc_695_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_env_675_; lean_object* v_checked_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_673_ = lean_st_ref_put(v___y_632_, v___x_672_);
v___x_674_ = lean_st_ref_get(v___y_634_);
v_env_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc_ref(v_env_675_);
lean_dec(v___x_674_);
v_checked_676_ = lean_ctor_get(v_env_675_, 2);
lean_inc_ref(v_checked_676_);
lean_dec_ref(v_env_675_);
v___x_677_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_678_ = l_Lean_traceBlock___redArg(v___x_677_, v_checked_676_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_toCold_679_; uint8_t v_isRecordingDeps_680_; lean_object* v_options_681_; uint8_t v___x_682_; uint8_t v___x_683_; 
lean_dec_ref_known(v___x_678_, 1);
v_toCold_679_ = lean_ctor_get(v___y_633_, 0);
v_isRecordingDeps_680_ = lean_ctor_get_uint8(v___y_633_, sizeof(void*)*3 + 4);
v_options_681_ = lean_ctor_get(v_toCold_679_, 2);
v___x_682_ = 1;
v___x_683_ = 0;
if (v_isRecordingDeps_680_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = l_Lean_Elab_async;
lean_inc_ref(v_options_681_);
v___x_685_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__3(v_options_681_, v___x_684_, v_isRecordingDeps_680_);
v___y_608_ = v___x_683_;
v___y_609_ = v___x_658_;
v___y_610_ = v___y_632_;
v___y_611_ = v___y_634_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_633_;
v___y_614_ = v___x_682_;
v___y_615_ = v___y_631_;
v___y_616_ = v___x_643_;
v___y_617_ = v___x_685_;
goto v___jp_607_;
}
else
{
lean_object* v___x_686_; 
lean_inc_ref(v_options_681_);
v___x_686_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_681_);
v___y_608_ = v___x_683_;
v___y_609_ = v___x_658_;
v___y_610_ = v___y_632_;
v___y_611_ = v___y_634_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_633_;
v___y_614_ = v___x_682_;
v___y_615_ = v___y_631_;
v___y_616_ = v___x_643_;
v___y_617_ = v___x_686_;
goto v___jp_607_;
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref_known(v___x_643_, 1);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_628_);
v_a_687_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_678_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_678_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
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
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_a_636_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
v_a_701_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_637_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_637_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v_checkType_261_);
v_a_709_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_635_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_635_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v_env_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_st_ref_get(v___y_267_);
v_env_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_env_719_);
lean_dec(v___x_718_);
v___x_720_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_721_ = l_Lean_Core_mkFreshUserName(v___x_720_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = l_Lean_mkPrivateName(v_env_719_, v_a_722_);
lean_dec_ref(v_env_719_);
v___x_724_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_263_, v___y_265_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_params_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_n(v_a_725_, 2);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_727_ = l_Lean_collectLevelParams(v___x_726_, v_a_725_);
v_params_728_ = lean_ctor_get(v___x_727_, 2);
lean_inc_ref(v_params_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = lean_box(0);
v___x_730_ = l_Lean_Expr_hasMVar(v_a_725_);
if (v___x_730_ == 0)
{
v___y_627_ = v___x_729_;
v___y_628_ = v___x_723_;
v___y_629_ = v_params_728_;
v___y_630_ = v_a_725_;
v___y_631_ = v___y_264_;
v___y_632_ = v___y_265_;
v___y_633_ = v___y_266_;
v___y_634_ = v___y_267_;
goto v___jp_626_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_725_);
v___x_732_ = l_Lean_indentExpr(v_a_725_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_733_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
v___y_627_ = v___x_729_;
v___y_628_ = v___x_723_;
v___y_629_ = v_params_728_;
v___y_630_ = v_a_725_;
v___y_631_ = v___y_264_;
v___y_632_ = v___y_265_;
v___y_633_ = v___y_266_;
v___y_634_ = v___y_267_;
goto v___jp_626_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_params_728_);
lean_dec(v_a_725_);
lean_dec(v___x_723_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_checkType_261_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v___x_723_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_checkType_261_);
v_a_743_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_724_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_724_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_env_719_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v_value_263_);
lean_dec_ref(v_checkType_261_);
v_a_751_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_721_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_721_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_759_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_mctx_773_; lean_object* v_zetaDeltaFVarIds_774_; lean_object* v_postponed_775_; lean_object* v_diag_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_785_; 
v___x_769_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_770_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_770_, 0, v___y_768_);
lean_ctor_set(v___x_770_, 1, v_nextMacroScope_760_);
lean_ctor_set(v___x_770_, 2, v_ngen_761_);
lean_ctor_set(v___x_770_, 3, v_auxDeclNGen_762_);
lean_ctor_set(v___x_770_, 4, v_traceState_763_);
lean_ctor_set(v___x_770_, 5, v___x_769_);
lean_ctor_set(v___x_770_, 6, v_recordedDeps_764_);
lean_ctor_set(v___x_770_, 7, v_messages_765_);
lean_ctor_set(v___x_770_, 8, v_infoState_766_);
lean_ctor_set(v___x_770_, 9, v_snapshotTasks_767_);
v___x_771_ = lean_st_ref_put(v___y_267_, v___x_770_);
v___x_772_ = lean_st_ref_take(v___y_265_);
v_mctx_773_ = lean_ctor_get(v___x_772_, 0);
v_zetaDeltaFVarIds_774_ = lean_ctor_get(v___x_772_, 2);
v_postponed_775_ = lean_ctor_get(v___x_772_, 3);
v_diag_776_ = lean_ctor_get(v___x_772_, 4);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_772_, 1);
lean_dec(v_unused_786_);
v___x_778_ = v___x_772_;
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_diag_776_);
lean_inc(v_postponed_775_);
lean_inc(v_zetaDeltaFVarIds_774_);
lean_inc(v_mctx_773_);
lean_dec(v___x_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_mctx_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_zetaDeltaFVarIds_774_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_postponed_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_diag_776_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_st_ref_put(v___y_265_, v___x_782_);
goto v___jp_717_;
}
}
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v_env_790_; lean_object* v_nextMacroScope_791_; lean_object* v_ngen_792_; lean_object* v_auxDeclNGen_793_; lean_object* v_traceState_794_; lean_object* v_recordedDeps_795_; lean_object* v_messages_796_; lean_object* v_infoState_797_; lean_object* v_snapshotTasks_798_; lean_object* v___x_799_; 
v___x_789_ = lean_st_ref_take(v___y_267_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref_n(v_env_790_, 2);
v_nextMacroScope_791_ = lean_ctor_get(v___x_789_, 1);
lean_inc(v_nextMacroScope_791_);
v_ngen_792_ = lean_ctor_get(v___x_789_, 2);
lean_inc_ref(v_ngen_792_);
v_auxDeclNGen_793_ = lean_ctor_get(v___x_789_, 3);
lean_inc_ref(v_auxDeclNGen_793_);
v_traceState_794_ = lean_ctor_get(v___x_789_, 4);
lean_inc_ref(v_traceState_794_);
v_recordedDeps_795_ = lean_ctor_get(v___x_789_, 6);
lean_inc_ref(v_recordedDeps_795_);
v_messages_796_ = lean_ctor_get(v___x_789_, 7);
lean_inc_ref(v_messages_796_);
v_infoState_797_ = lean_ctor_get(v___x_789_, 8);
lean_inc_ref(v_infoState_797_);
v_snapshotTasks_798_ = lean_ctor_get(v___x_789_, 9);
lean_inc_ref(v_snapshotTasks_798_);
lean_dec(v___x_789_);
v___x_799_ = l_Lean_Environment_importEnv_x3f(v_env_790_);
if (lean_obj_tag(v___x_799_) == 0)
{
v_nextMacroScope_760_ = v_nextMacroScope_791_;
v_ngen_761_ = v_ngen_792_;
v_auxDeclNGen_762_ = v_auxDeclNGen_793_;
v_traceState_763_ = v_traceState_794_;
v_recordedDeps_764_ = v_recordedDeps_795_;
v_messages_765_ = v_messages_796_;
v_infoState_766_ = v_infoState_797_;
v_snapshotTasks_767_ = v_snapshotTasks_798_;
v___y_768_ = v_env_790_;
goto v___jp_759_;
}
else
{
lean_object* v_val_800_; 
lean_dec_ref(v_env_790_);
v_val_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v___x_799_, 1);
v_nextMacroScope_760_ = v_nextMacroScope_791_;
v_ngen_761_ = v_ngen_792_;
v_auxDeclNGen_762_ = v_auxDeclNGen_793_;
v_traceState_763_ = v_traceState_794_;
v_recordedDeps_764_ = v_recordedDeps_795_;
v_messages_765_ = v_messages_796_;
v_infoState_766_ = v_infoState_797_;
v_snapshotTasks_767_ = v_snapshotTasks_798_;
v___y_768_ = v_val_800_;
goto v___jp_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_809_, lean_object* v_checkType_810_, lean_object* v_safety_811_, lean_object* v_value_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v_checkMeta_boxed_818_; uint8_t v_safety_boxed_819_; lean_object* v_res_820_; 
v_checkMeta_boxed_818_ = lean_unbox(v_checkMeta_809_);
v_safety_boxed_819_ = lean_unbox(v_safety_811_);
v_res_820_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_818_, v_checkType_810_, v_safety_boxed_819_, v_value_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object* v_env_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_nextMacroScope_826_; lean_object* v_ngen_827_; lean_object* v_auxDeclNGen_828_; lean_object* v_traceState_829_; lean_object* v_recordedDeps_830_; lean_object* v_messages_831_; lean_object* v_infoState_832_; lean_object* v_snapshotTasks_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_859_; 
v___x_825_ = lean_st_ref_take(v___y_823_);
v_nextMacroScope_826_ = lean_ctor_get(v___x_825_, 1);
v_ngen_827_ = lean_ctor_get(v___x_825_, 2);
v_auxDeclNGen_828_ = lean_ctor_get(v___x_825_, 3);
v_traceState_829_ = lean_ctor_get(v___x_825_, 4);
v_recordedDeps_830_ = lean_ctor_get(v___x_825_, 6);
v_messages_831_ = lean_ctor_get(v___x_825_, 7);
v_infoState_832_ = lean_ctor_get(v___x_825_, 8);
v_snapshotTasks_833_ = lean_ctor_get(v___x_825_, 9);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; lean_object* v_unused_861_; 
v_unused_860_ = lean_ctor_get(v___x_825_, 5);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v___x_825_, 0);
lean_dec(v_unused_861_);
v___x_835_ = v___x_825_;
v_isShared_836_ = v_isSharedCheck_859_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snapshotTasks_833_);
lean_inc(v_infoState_832_);
lean_inc(v_messages_831_);
lean_inc(v_recordedDeps_830_);
lean_inc(v_traceState_829_);
lean_inc(v_auxDeclNGen_828_);
lean_inc(v_ngen_827_);
lean_inc(v_nextMacroScope_826_);
lean_dec(v___x_825_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_859_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 5, v___x_837_);
lean_ctor_set(v___x_835_, 0, v_env_821_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_env_821_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_nextMacroScope_826_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_ngen_827_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_auxDeclNGen_828_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_traceState_829_);
lean_ctor_set(v_reuseFailAlloc_858_, 5, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_858_, 6, v_recordedDeps_830_);
lean_ctor_set(v_reuseFailAlloc_858_, 7, v_messages_831_);
lean_ctor_set(v_reuseFailAlloc_858_, 8, v_infoState_832_);
lean_ctor_set(v_reuseFailAlloc_858_, 9, v_snapshotTasks_833_);
v___x_839_ = v_reuseFailAlloc_858_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_mctx_842_; lean_object* v_zetaDeltaFVarIds_843_; lean_object* v_postponed_844_; lean_object* v_diag_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_856_; 
v___x_840_ = lean_st_ref_put(v___y_823_, v___x_839_);
v___x_841_ = lean_st_ref_take(v___y_822_);
v_mctx_842_ = lean_ctor_get(v___x_841_, 0);
v_zetaDeltaFVarIds_843_ = lean_ctor_get(v___x_841_, 2);
v_postponed_844_ = lean_ctor_get(v___x_841_, 3);
v_diag_845_ = lean_ctor_get(v___x_841_, 4);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v___x_841_, 1);
lean_dec(v_unused_857_);
v___x_847_ = v___x_841_;
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_diag_845_);
lean_inc(v_postponed_844_);
lean_inc(v_zetaDeltaFVarIds_843_);
lean_inc(v_mctx_842_);
lean_dec(v___x_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_850_);
v___x_852_ = v___x_847_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_mctx_842_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_zetaDeltaFVarIds_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_postponed_844_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_diag_845_);
v___x_852_ = v_reuseFailAlloc_855_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_st_ref_put(v___y_822_, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_849_);
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object* v_env_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object* v_env_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; lean_object* v_env_875_; lean_object* v_a_877_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_874_ = lean_st_ref_get(v___y_872_);
v_env_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_env_875_);
lean_dec(v___x_874_);
v___x_887_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_867_, v___y_870_, v___y_872_);
lean_dec_ref(v___x_887_);
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
lean_inc(v___y_870_);
lean_inc_ref(v___y_869_);
v___x_888_ = lean_apply_5(v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, lean_box(0));
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_875_, v___y_870_, v___y_872_);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_890_, 0);
lean_dec(v_unused_898_);
v___x_892_ = v___x_890_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_a_889_);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_899_; 
v_a_899_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_888_, 1);
v_a_877_ = v_a_899_;
goto v___jp_876_;
}
v___jp_876_:
{
lean_object* v___x_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v___x_878_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_875_, v___y_870_, v___y_872_);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_886_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 1);
lean_ctor_set(v___x_880_, 0, v_a_877_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object* v_env_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_908_, lean_object* v_checkType_909_, uint8_t v_safety_910_, uint8_t v_checkMeta_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v_env_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = lean_box(v_checkMeta_911_);
v___x_918_ = lean_box(v_safety_910_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_919_, 0, v___x_917_);
lean_closure_set(v___f_919_, 1, v_checkType_909_);
lean_closure_set(v___f_919_, 2, v___x_918_);
lean_closure_set(v___f_919_, 3, v_value_908_);
v___x_920_ = lean_st_ref_get(v_a_915_);
v_env_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_env_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_Environment_unlockAsync(v_env_921_);
v___x_923_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v___x_922_, v___f_919_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_924_, lean_object* v_checkType_925_, lean_object* v_safety_926_, lean_object* v_checkMeta_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_safety_boxed_933_; uint8_t v_checkMeta_boxed_934_; lean_object* v_res_935_; 
v_safety_boxed_933_ = lean_unbox(v_safety_926_);
v_checkMeta_boxed_934_ = lean_unbox(v_checkMeta_927_);
v_res_935_ = l_Lean_Meta_evalExprCore___redArg(v_value_924_, v_checkType_925_, v_safety_boxed_933_, v_checkMeta_boxed_934_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_936_, lean_object* v_value_937_, lean_object* v_checkType_938_, uint8_t v_safety_939_, uint8_t v_checkMeta_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Meta_evalExprCore___redArg(v_value_937_, v_checkType_938_, v_safety_939_, v_checkMeta_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_947_, lean_object* v_value_948_, lean_object* v_checkType_949_, lean_object* v_safety_950_, lean_object* v_checkMeta_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_safety_boxed_957_; uint8_t v_checkMeta_boxed_958_; lean_object* v_res_959_; 
v_safety_boxed_957_ = lean_unbox(v_safety_950_);
v_checkMeta_boxed_958_ = lean_unbox(v_checkMeta_951_);
v_res_959_ = l_Lean_Meta_evalExprCore(v_00_u03b1_947_, v_value_948_, v_checkType_949_, v_safety_boxed_957_, v_checkMeta_boxed_958_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(lean_object* v_00_u03b1_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___redArg();
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3___boxed(lean_object* v_00_u03b1_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__3(v_00_u03b1_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_00_u03b1_974_, lean_object* v_constName_975_, uint8_t v_checkMeta_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___redArg(v_constName_975_, v_checkMeta_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_00_u03b1_983_, lean_object* v_constName_984_, lean_object* v_checkMeta_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v_checkMeta_boxed_991_; lean_object* v_res_992_; 
v_checkMeta_boxed_991_ = lean_unbox(v_checkMeta_985_);
v_res_992_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2(v_00_u03b1_983_, v_constName_984_, v_checkMeta_boxed_991_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_993_, lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_1001_, v_msg_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object* v_env_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_1009_, v___y_1011_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object* v_env_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v_00_u03b1_1023_, lean_object* v_env_1024_, lean_object* v_x_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_1024_, v_x_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v_00_u03b1_1032_, lean_object* v_env_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(v_00_u03b1_1032_, v_env_1033_, v_x_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(lean_object* v_00_u03b1_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___redArg(v_x_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__2_spec__2(v_00_u03b1_1049_, v_x_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1060_, lean_object* v_type_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_whnfD(v_type_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1081_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Lean_Expr_isConstOf(v_a_1068_, v_typeName_1060_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_del_object(v___x_1070_);
v___x_1073_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1074_ = l_Lean_indentExpr(v_a_1068_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1075_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v_a_1068_);
v___x_1077_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1077_);
v___x_1079_ = v___x_1070_;
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
v_a_1082_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1067_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1067_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1090_, lean_object* v_type_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1090_, v_type_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_typeName_1090_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1098_, lean_object* v_value_1099_, uint8_t v_safety_1100_, uint8_t v_checkMeta_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1107_, 0, v_typeName_1098_);
v___x_1108_ = l_Lean_Meta_evalExprCore___redArg(v_value_1099_, v___f_1107_, v_safety_1100_, v_checkMeta_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1109_, lean_object* v_value_1110_, lean_object* v_safety_1111_, lean_object* v_checkMeta_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
uint8_t v_safety_boxed_1118_; uint8_t v_checkMeta_boxed_1119_; lean_object* v_res_1120_; 
v_safety_boxed_1118_ = lean_unbox(v_safety_1111_);
v_checkMeta_boxed_1119_ = lean_unbox(v_checkMeta_1112_);
v_res_1120_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1109_, v_value_1110_, v_safety_boxed_1118_, v_checkMeta_boxed_1119_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1121_, lean_object* v_typeName_1122_, lean_object* v_value_1123_, uint8_t v_safety_1124_, uint8_t v_checkMeta_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1122_, v_value_1123_, v_safety_1124_, v_checkMeta_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_typeName_1133_, lean_object* v_value_1134_, lean_object* v_safety_1135_, lean_object* v_checkMeta_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
uint8_t v_safety_boxed_1142_; uint8_t v_checkMeta_boxed_1143_; lean_object* v_res_1144_; 
v_safety_boxed_1142_ = lean_unbox(v_safety_1135_);
v_checkMeta_boxed_1143_ = lean_unbox(v_checkMeta_1136_);
v_res_1144_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1132_, v_typeName_1133_, v_value_1134_, v_safety_boxed_1142_, v_checkMeta_boxed_1143_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1144_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1150_, lean_object* v_type_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
lean_inc_ref(v_expectedType_1150_);
lean_inc_ref(v_type_1151_);
v___x_1157_ = l_Lean_Meta_isExprDefEq(v_type_1151_, v_expectedType_1150_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1182_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1160_);
v___x_1163_ = lean_box(0);
v___x_1164_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1165_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1151_, v_expectedType_1150_, v___x_1163_, v___x_1164_, v___y_1152_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v_a_1166_);
v___x_1169_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1168_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1169_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1165_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1165_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
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
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_dec_ref(v_type_1151_);
lean_dec_ref(v_expectedType_1150_);
v___x_1178_ = lean_box(0);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1178_);
v___x_1180_ = v___x_1160_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_type_1151_);
lean_dec_ref(v_expectedType_1150_);
v_a_1183_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1157_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1157_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1191_, lean_object* v_type_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1191_, v_type_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1199_, lean_object* v_value_1200_, uint8_t v_safety_1201_, uint8_t v_checkMeta_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___f_1208_; lean_object* v___x_1209_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1208_, 0, v_expectedType_1199_);
v___x_1209_ = l_Lean_Meta_evalExprCore___redArg(v_value_1200_, v___f_1208_, v_safety_1201_, v_checkMeta_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1210_, lean_object* v_value_1211_, lean_object* v_safety_1212_, lean_object* v_checkMeta_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
uint8_t v_safety_boxed_1219_; uint8_t v_checkMeta_boxed_1220_; lean_object* v_res_1221_; 
v_safety_boxed_1219_ = lean_unbox(v_safety_1212_);
v_checkMeta_boxed_1220_ = lean_unbox(v_checkMeta_1213_);
v_res_1221_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1210_, v_value_1211_, v_safety_boxed_1219_, v_checkMeta_boxed_1220_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1222_, lean_object* v_expectedType_1223_, lean_object* v_value_1224_, uint8_t v_safety_1225_, uint8_t v_checkMeta_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1223_, v_value_1224_, v_safety_1225_, v_checkMeta_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_expectedType_1234_, lean_object* v_value_1235_, lean_object* v_safety_1236_, lean_object* v_checkMeta_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
uint8_t v_safety_boxed_1243_; uint8_t v_checkMeta_boxed_1244_; lean_object* v_res_1245_; 
v_safety_boxed_1243_ = lean_unbox(v_safety_1236_);
v_checkMeta_boxed_1244_ = lean_unbox(v_checkMeta_1237_);
v_res_1245_ = l_Lean_Meta_evalExpr(v_00_u03b1_1233_, v_expectedType_1234_, v_value_1235_, v_safety_boxed_1243_, v_checkMeta_boxed_1244_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1245_;
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

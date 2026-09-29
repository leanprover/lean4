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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_opts_44_, lean_object* v_opt_45_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_opts_52_, lean_object* v_opt_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_52_, v_opt_53_);
lean_dec_ref(v_opt_53_);
lean_dec_ref(v_opts_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; lean_object* v_toCold_64_; lean_object* v_mctx_65_; lean_object* v_lctx_66_; lean_object* v_options_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_61_ = lean_st_ref_get(v___y_59_);
v_env_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_env_62_);
lean_dec(v___x_61_);
v___x_63_ = lean_st_ref_get(v___y_57_);
v_toCold_64_ = lean_ctor_get(v___y_58_, 0);
v_mctx_65_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_mctx_65_);
lean_dec(v___x_63_);
v_lctx_66_ = lean_ctor_get(v___y_56_, 2);
v_options_67_ = lean_ctor_get(v_toCold_64_, 2);
lean_inc_ref(v_options_67_);
lean_inc_ref(v_lctx_66_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_env_62_);
lean_ctor_set(v___x_68_, 1, v_mctx_65_);
lean_ctor_set(v___x_68_, 2, v_lctx_66_);
lean_ctor_set(v___x_68_, 3, v_options_67_);
v___x_69_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_msgData_55_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object* v_msgData_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msgData_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_ref_84_ = lean_ctor_get(v___y_81_, 2);
v___x_85_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_msg_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
lean_inc(v_ref_84_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_ref_84_);
lean_ctor_set(v___x_90_, 1, v_a_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_a_108_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v_x_102_, 1);
v___x_109_ = l_Lean_stringToMessageData(v_a_108_);
v___x_110_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_109_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v_x_102_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v_x_102_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v_x_102_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 0);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg___boxed(lean_object* v_x_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = l_Lean_Elab_abortCommandExceptionId;
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg(){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___boxed(lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(lean_object* v_constName_134_, uint8_t v_checkMeta_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; lean_object* v_env_142_; uint8_t v___x_143_; 
v___x_141_ = lean_st_ref_get(v___y_139_);
v_env_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_env_142_);
lean_dec(v___x_141_);
lean_inc(v_constName_134_);
v___x_143_ = lean_has_compile_error(v_env_142_, v_constName_134_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v_env_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = lean_st_ref_get(v___y_139_);
v_env_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc_ref(v_env_145_);
lean_dec(v___x_144_);
v___x_146_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_138_);
v___x_147_ = l_Lean_Environment_evalConst___redArg(v_env_145_, v___x_146_, v_constName_134_, v_checkMeta_135_);
lean_dec(v_constName_134_);
lean_dec_ref(v___x_146_);
lean_dec_ref(v_env_145_);
v___x_148_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v___x_147_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v___x_150_; lean_object* v_env_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref_known(v___x_149_, 1);
v___x_150_ = lean_st_ref_get(v___y_139_);
v_env_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc_ref(v_env_151_);
lean_dec(v___x_150_);
v___x_152_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_138_);
v___x_153_ = l_Lean_Environment_evalConst___redArg(v_env_151_, v___x_152_, v_constName_134_, v_checkMeta_135_);
lean_dec(v_constName_134_);
lean_dec_ref(v___x_152_);
lean_dec_ref(v_env_151_);
v___x_154_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v___x_153_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
return v___x_154_;
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_constName_134_);
v_a_155_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_149_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_149_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg___boxed(lean_object* v_constName_163_, lean_object* v_checkMeta_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v_checkMeta_boxed_170_; lean_object* v_res_171_; 
v_checkMeta_boxed_170_ = lean_unbox(v_checkMeta_164_);
v_res_171_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_163_, v_checkMeta_boxed_170_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_171_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v___x_172_, lean_object* v___x_173_, lean_object* v_as_174_, size_t v_i_175_, size_t v_stop_176_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_eq(v_i_175_, v_stop_176_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_array_uget_borrowed(v_as_174_, v_i_175_);
v___x_183_ = l_Lean_Environment_isImportedConst(v___x_172_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_nat_dec_lt(v___x_184_, v___x_173_);
if (v___x_185_ == 0)
{
goto v___jp_177_;
}
else
{
return v___x_185_;
}
}
else
{
goto v___jp_177_;
}
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
v___jp_177_:
{
size_t v___x_178_; size_t v___x_179_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_175_, v___x_178_);
v_i_175_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_stop_191_){
_start:
{
size_t v_i_boxed_192_; size_t v_stop_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_stop_boxed_193_ = lean_unbox_usize(v_stop_191_);
lean_dec(v_stop_191_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v___x_187_, v___x_188_, v_as_189_, v_i_boxed_192_, v_stop_boxed_193_);
lean_dec_ref(v_as_189_);
lean_dec(v___x_188_);
lean_dec_ref(v___x_187_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_o_199_, lean_object* v_k_200_, uint8_t v_v_201_){
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
v___x_209_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* v_o_218_, lean_object* v_k_219_, lean_object* v_v_220_){
_start:
{
uint8_t v_v_boxed_221_; lean_object* v_res_222_; 
v_v_boxed_221_ = lean_unbox(v_v_220_);
v_res_222_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_o_218_, v_k_219_, v_v_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_223_, lean_object* v_opt_224_, uint8_t v_val_225_){
_start:
{
lean_object* v_name_226_; lean_object* v___x_227_; 
v_name_226_ = lean_ctor_get(v_opt_224_, 0);
lean_inc(v_name_226_);
lean_dec_ref(v_opt_224_);
v___x_227_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_opts_223_, v_name_226_, v_val_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_228_, lean_object* v_opt_229_, lean_object* v_val_230_){
_start:
{
uint8_t v_val_boxed_231_; lean_object* v_res_232_; 
v_val_boxed_231_ = lean_unbox(v_val_230_);
v_res_232_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_opts_228_, v_opt_229_, v_val_boxed_231_);
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
uint8_t v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; uint16_t v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; uint8_t v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; uint8_t v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; uint8_t v___y_332_; uint16_t v___y_333_; lean_object* v___y_334_; uint8_t v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; uint8_t v___y_366_; uint16_t v___y_367_; lean_object* v___y_368_; uint8_t v___y_369_; lean_object* v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint16_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_426_; uint8_t v___y_427_; lean_object* v___y_428_; uint8_t v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint16_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; uint16_t v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v___y_475_; uint16_t v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v_fileName_484_; lean_object* v_fileMap_485_; lean_object* v_currNamespace_486_; lean_object* v_openDecls_487_; lean_object* v_initHeartbeats_488_; lean_object* v_maxHeartbeats_489_; lean_object* v_quotContext_490_; lean_object* v_currMacroScope_491_; lean_object* v_cancelTk_x3f_492_; lean_object* v_inheritedTraceOptions_493_; lean_object* v_currRecDepth_494_; lean_object* v_ref_495_; uint8_t v_suppressElabErrors_496_; uint8_t v_isRecordingDeps_497_; lean_object* v___y_498_; lean_object* v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; uint8_t v___y_519_; lean_object* v___y_520_; uint16_t v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_nextMacroScope_715_; lean_object* v_ngen_716_; lean_object* v_auxDeclNGen_717_; lean_object* v_traceState_718_; lean_object* v_recordedDeps_719_; lean_object* v_messages_720_; lean_object* v_infoState_721_; lean_object* v_snapshotTasks_722_; lean_object* v___y_723_; lean_object* v___x_742_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_742_ = lean_st_ref_get(v___y_265_);
lean_inc_ref(v_value_261_);
v___x_756_ = l_Lean_Expr_getUsedConstants(v_value_261_);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_array_get_size(v___x_756_);
v___x_759_ = lean_nat_dec_lt(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec_ref(v___x_756_);
lean_dec(v___x_742_);
goto v___jp_743_;
}
else
{
if (v___x_759_ == 0)
{
lean_dec_ref(v___x_756_);
lean_dec(v___x_742_);
goto v___jp_743_;
}
else
{
lean_object* v_env_760_; size_t v___x_761_; size_t v___x_762_; uint8_t v___x_763_; 
v_env_760_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_760_);
lean_dec(v___x_742_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_758_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__5(v_env_760_, v___x_758_, v___x_756_, v___x_761_, v___x_762_);
lean_dec_ref(v___x_756_);
lean_dec_ref(v_env_760_);
if (v___x_763_ == 0)
{
goto v___jp_743_;
}
else
{
goto v___jp_672_;
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
v___x_300_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_274_, v___y_269_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 3, v___x_300_);
lean_ctor_set(v___x_298_, 2, v___y_274_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fileName_287_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_fileMap_288_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v___y_274_);
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
v___x_305_ = l_Lean_addAndCompile(v___y_273_, v___y_272_, v___y_268_, v___x_304_, v___y_278_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v___x_306_; 
lean_dec_ref_known(v___x_305_, 1);
v___x_306_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v___y_271_, v_checkMeta_258_, v___y_270_, v___y_275_, v___x_304_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___x_304_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_270_);
return v___x_306_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v___x_304_);
lean_dec(v___y_278_);
lean_dec(v___y_275_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
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
v___x_335_ = lean_st_ref_take(v___y_325_);
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
v___x_348_ = l_Lean_Kernel_enableDiag(v_env_336_, v___y_326_);
lean_inc_ref(v___y_329_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 5, v___y_329_);
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
lean_ctor_set(v_reuseFailAlloc_352_, 5, v___y_329_);
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
v___x_351_ = lean_st_ref_put(v___y_325_, v___x_350_);
v___y_268_ = v___y_322_;
v___y_269_ = v___y_323_;
v___y_270_ = v___y_324_;
v___y_271_ = v___y_330_;
v___y_272_ = v___y_332_;
v___y_273_ = v___y_327_;
v___y_274_ = v___y_328_;
v___y_275_ = v___y_334_;
v___y_276_ = v___y_333_;
v___y_277_ = v___y_331_;
v___y_278_ = v___y_325_;
goto v___jp_267_;
}
}
}
v___jp_355_:
{
if (v___y_369_ == 0)
{
if (v___y_366_ == 0)
{
v___y_268_ = v___y_356_;
v___y_269_ = v___y_357_;
v___y_270_ = v___y_358_;
v___y_271_ = v___y_363_;
v___y_272_ = v___y_365_;
v___y_273_ = v___y_360_;
v___y_274_ = v___y_361_;
v___y_275_ = v___y_368_;
v___y_276_ = v___y_367_;
v___y_277_ = v___y_364_;
v___y_278_ = v___y_359_;
goto v___jp_267_;
}
else
{
v___y_322_ = v___y_356_;
v___y_323_ = v___y_357_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_369_;
v___y_327_ = v___y_360_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
goto v___jp_321_;
}
}
else
{
if (v___y_366_ == 0)
{
v___y_322_ = v___y_356_;
v___y_323_ = v___y_357_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_369_;
v___y_327_ = v___y_360_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
goto v___jp_321_;
}
else
{
v___y_268_ = v___y_356_;
v___y_269_ = v___y_357_;
v___y_270_ = v___y_358_;
v___y_271_ = v___y_363_;
v___y_272_ = v___y_365_;
v___y_273_ = v___y_360_;
v___y_274_ = v___y_361_;
v___y_275_ = v___y_368_;
v___y_276_ = v___y_367_;
v___y_277_ = v___y_364_;
v___y_278_ = v___y_359_;
goto v___jp_267_;
}
}
}
v___jp_370_:
{
lean_object* v_toCold_383_; lean_object* v_currRecDepth_384_; lean_object* v_ref_385_; uint8_t v_suppressElabErrors_386_; uint8_t v_isRecordingDeps_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_424_; 
v_toCold_383_ = lean_ctor_get(v___y_381_, 0);
v_currRecDepth_384_ = lean_ctor_get(v___y_381_, 1);
v_ref_385_ = lean_ctor_get(v___y_381_, 2);
v_suppressElabErrors_386_ = lean_ctor_get_uint8(v___y_381_, sizeof(void*)*3 + 2);
v_isRecordingDeps_387_ = lean_ctor_get_uint8(v___y_381_, sizeof(void*)*3 + 3);
v_isSharedCheck_424_ = !lean_is_exclusive(v___y_381_);
if (v_isSharedCheck_424_ == 0)
{
v___x_389_ = v___y_381_;
v_isShared_390_ = v_isSharedCheck_424_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_ref_385_);
lean_inc(v_currRecDepth_384_);
lean_inc(v_toCold_383_);
lean_dec(v___y_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_424_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_fileName_391_; lean_object* v_fileMap_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_quotContext_397_; lean_object* v_currMacroScope_398_; lean_object* v_cancelTk_x3f_399_; lean_object* v_inheritedTraceOptions_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_421_; 
v_fileName_391_ = lean_ctor_get(v_toCold_383_, 0);
v_fileMap_392_ = lean_ctor_get(v_toCold_383_, 1);
v_currNamespace_393_ = lean_ctor_get(v_toCold_383_, 4);
v_openDecls_394_ = lean_ctor_get(v_toCold_383_, 5);
v_initHeartbeats_395_ = lean_ctor_get(v_toCold_383_, 6);
v_maxHeartbeats_396_ = lean_ctor_get(v_toCold_383_, 7);
v_quotContext_397_ = lean_ctor_get(v_toCold_383_, 8);
v_currMacroScope_398_ = lean_ctor_get(v_toCold_383_, 9);
v_cancelTk_x3f_399_ = lean_ctor_get(v_toCold_383_, 10);
v_inheritedTraceOptions_400_ = lean_ctor_get(v_toCold_383_, 11);
v_isSharedCheck_421_ = !lean_is_exclusive(v_toCold_383_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; lean_object* v_unused_423_; 
v_unused_422_ = lean_ctor_get(v_toCold_383_, 3);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_toCold_383_, 2);
lean_dec(v_unused_423_);
v___x_402_ = v_toCold_383_;
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_inheritedTraceOptions_400_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc(v_fileMap_392_);
lean_inc(v_fileName_391_);
lean_dec(v_toCold_383_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_377_, v___y_373_);
lean_inc_ref(v___y_377_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 3, v___x_404_);
lean_ctor_set(v___x_402_, 2, v___y_377_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_fileName_391_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_fileMap_392_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___y_377_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_currNamespace_393_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_openDecls_394_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_initHeartbeats_395_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_maxHeartbeats_396_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_quotContext_397_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_currMacroScope_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 10, v_cancelTk_x3f_399_);
lean_ctor_set(v_reuseFailAlloc_420_, 11, v_inheritedTraceOptions_400_);
v___x_406_ = v_reuseFailAlloc_420_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_406_);
v___x_408_ = v___x_389_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_currRecDepth_384_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_ref_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 2, v_suppressElabErrors_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 3, v_isRecordingDeps_387_);
v___x_408_ = v_reuseFailAlloc_419_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint16_t v___x_411_; lean_object* v___x_412_; lean_object* v_env_413_; uint8_t v___x_414_; uint16_t v___x_415_; uint16_t v___x_416_; uint16_t v___x_417_; uint8_t v___x_418_; 
lean_ctor_set_uint16(v___x_408_, sizeof(void*)*3, v___y_380_);
v___x_409_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_410_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_377_, v___x_409_, v___y_376_);
v___x_411_ = l_Lean_OptionFlags_ofOptions(v___x_410_);
v___x_412_ = lean_st_ref_get(v___y_382_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_env_413_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_413_);
lean_dec_ref(v_env_413_);
v___x_415_ = 512;
v___x_416_ = lean_uint16_land(v___x_411_, v___x_415_);
v___x_417_ = 0;
v___x_418_ = lean_uint16_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
v___y_356_ = v___y_372_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_375_;
v___y_359_ = v___y_382_;
v___y_360_ = v___y_378_;
v___y_361_ = v___x_410_;
v___y_362_ = v___y_371_;
v___y_363_ = v___y_374_;
v___y_364_ = v___x_408_;
v___y_365_ = v___y_376_;
v___y_366_ = v___x_414_;
v___y_367_ = v___x_411_;
v___y_368_ = v___y_379_;
v___y_369_ = v___y_376_;
goto v___jp_355_;
}
else
{
v___y_356_ = v___y_372_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_375_;
v___y_359_ = v___y_382_;
v___y_360_ = v___y_378_;
v___y_361_ = v___x_410_;
v___y_362_ = v___y_371_;
v___y_363_ = v___y_374_;
v___y_364_ = v___x_408_;
v___y_365_ = v___y_376_;
v___y_366_ = v___x_414_;
v___y_367_ = v___x_411_;
v___y_368_ = v___y_379_;
v___y_369_ = v___y_372_;
goto v___jp_355_;
}
}
}
}
}
}
v___jp_425_:
{
lean_object* v___x_439_; lean_object* v_env_440_; lean_object* v_nextMacroScope_441_; lean_object* v_ngen_442_; lean_object* v_auxDeclNGen_443_; lean_object* v_traceState_444_; lean_object* v_recordedDeps_445_; lean_object* v_messages_446_; lean_object* v_infoState_447_; lean_object* v_snapshotTasks_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v___x_439_ = lean_st_ref_take(v___y_426_);
v_env_440_ = lean_ctor_get(v___x_439_, 0);
v_nextMacroScope_441_ = lean_ctor_get(v___x_439_, 1);
v_ngen_442_ = lean_ctor_get(v___x_439_, 2);
v_auxDeclNGen_443_ = lean_ctor_get(v___x_439_, 3);
v_traceState_444_ = lean_ctor_get(v___x_439_, 4);
v_recordedDeps_445_ = lean_ctor_get(v___x_439_, 6);
v_messages_446_ = lean_ctor_get(v___x_439_, 7);
v_infoState_447_ = lean_ctor_get(v___x_439_, 8);
v_snapshotTasks_448_ = lean_ctor_get(v___x_439_, 9);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_439_, 5);
lean_dec(v_unused_458_);
v___x_450_ = v___x_439_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_snapshotTasks_448_);
lean_inc(v_infoState_447_);
lean_inc(v_messages_446_);
lean_inc(v_recordedDeps_445_);
lean_inc(v_traceState_444_);
lean_inc(v_auxDeclNGen_443_);
lean_inc(v_ngen_442_);
lean_inc(v_nextMacroScope_441_);
lean_inc(v_env_440_);
lean_dec(v___x_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Lean_Kernel_enableDiag(v_env_440_, v___y_429_);
lean_inc_ref(v___y_433_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 5, v___y_433_);
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_nextMacroScope_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_ngen_442_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_auxDeclNGen_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_traceState_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v___y_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_recordedDeps_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_messages_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_infoState_447_);
lean_ctor_set(v_reuseFailAlloc_456_, 9, v_snapshotTasks_448_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_st_ref_put(v___y_426_, v___x_454_);
v___y_371_ = v___y_433_;
v___y_372_ = v___y_427_;
v___y_373_ = v___y_428_;
v___y_374_ = v___y_434_;
v___y_375_ = v___y_430_;
v___y_376_ = v___y_436_;
v___y_377_ = v___y_431_;
v___y_378_ = v___y_432_;
v___y_379_ = v___y_438_;
v___y_380_ = v___y_437_;
v___y_381_ = v___y_435_;
v___y_382_ = v___y_426_;
goto v___jp_370_;
}
}
}
v___jp_459_:
{
if (v___y_473_ == 0)
{
if (v___y_467_ == 0)
{
v___y_371_ = v___y_466_;
v___y_372_ = v___y_461_;
v___y_373_ = v___y_462_;
v___y_374_ = v___y_468_;
v___y_375_ = v___y_463_;
v___y_376_ = v___y_470_;
v___y_377_ = v___y_464_;
v___y_378_ = v___y_465_;
v___y_379_ = v___y_472_;
v___y_380_ = v___y_471_;
v___y_381_ = v___y_469_;
v___y_382_ = v___y_460_;
goto v___jp_370_;
}
else
{
v___y_426_ = v___y_460_;
v___y_427_ = v___y_461_;
v___y_428_ = v___y_462_;
v___y_429_ = v___y_473_;
v___y_430_ = v___y_463_;
v___y_431_ = v___y_464_;
v___y_432_ = v___y_465_;
v___y_433_ = v___y_466_;
v___y_434_ = v___y_468_;
v___y_435_ = v___y_469_;
v___y_436_ = v___y_470_;
v___y_437_ = v___y_471_;
v___y_438_ = v___y_472_;
goto v___jp_425_;
}
}
else
{
if (v___y_467_ == 0)
{
v___y_426_ = v___y_460_;
v___y_427_ = v___y_461_;
v___y_428_ = v___y_462_;
v___y_429_ = v___y_473_;
v___y_430_ = v___y_463_;
v___y_431_ = v___y_464_;
v___y_432_ = v___y_465_;
v___y_433_ = v___y_466_;
v___y_434_ = v___y_468_;
v___y_435_ = v___y_469_;
v___y_436_ = v___y_470_;
v___y_437_ = v___y_471_;
v___y_438_ = v___y_472_;
goto v___jp_425_;
}
else
{
v___y_371_ = v___y_466_;
v___y_372_ = v___y_461_;
v___y_373_ = v___y_462_;
v___y_374_ = v___y_468_;
v___y_375_ = v___y_463_;
v___y_376_ = v___y_470_;
v___y_377_ = v___y_464_;
v___y_378_ = v___y_465_;
v___y_379_ = v___y_472_;
v___y_380_ = v___y_471_;
v___y_381_ = v___y_469_;
v___y_382_ = v___y_460_;
goto v___jp_370_;
}
}
}
v___jp_474_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint16_t v___x_505_; lean_object* v___x_506_; lean_object* v_env_507_; uint8_t v___x_508_; uint16_t v___x_509_; uint16_t v___x_510_; uint16_t v___x_511_; uint8_t v___x_512_; 
v___x_499_ = l_Lean_maxRecDepth;
v___x_500_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_477_, v___x_499_);
lean_inc_ref(v___y_477_);
v___x_501_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_501_, 0, v_fileName_484_);
lean_ctor_set(v___x_501_, 1, v_fileMap_485_);
lean_ctor_set(v___x_501_, 2, v___y_477_);
lean_ctor_set(v___x_501_, 3, v___x_500_);
lean_ctor_set(v___x_501_, 4, v_currNamespace_486_);
lean_ctor_set(v___x_501_, 5, v_openDecls_487_);
lean_ctor_set(v___x_501_, 6, v_initHeartbeats_488_);
lean_ctor_set(v___x_501_, 7, v_maxHeartbeats_489_);
lean_ctor_set(v___x_501_, 8, v_quotContext_490_);
lean_ctor_set(v___x_501_, 9, v_currMacroScope_491_);
lean_ctor_set(v___x_501_, 10, v_cancelTk_x3f_492_);
lean_ctor_set(v___x_501_, 11, v_inheritedTraceOptions_493_);
v___x_502_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_currRecDepth_494_);
lean_ctor_set(v___x_502_, 2, v_ref_495_);
lean_ctor_set_uint16(v___x_502_, sizeof(void*)*3, v___y_476_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 2, v_suppressElabErrors_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 3, v_isRecordingDeps_497_);
v___x_503_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_504_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_477_, v___x_503_, v___y_478_);
v___x_505_ = l_Lean_OptionFlags_ofOptions(v___x_504_);
v___x_506_ = lean_st_ref_get(v___y_498_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_507_);
lean_dec_ref(v_env_507_);
v___x_509_ = 512;
v___x_510_ = lean_uint16_land(v___x_505_, v___x_509_);
v___x_511_ = 0;
v___x_512_ = lean_uint16_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
v___y_460_ = v___y_498_;
v___y_461_ = v___y_478_;
v___y_462_ = v___x_499_;
v___y_463_ = v___y_479_;
v___y_464_ = v___x_504_;
v___y_465_ = v___y_482_;
v___y_466_ = v___y_475_;
v___y_467_ = v___x_508_;
v___y_468_ = v___y_480_;
v___y_469_ = v___x_502_;
v___y_470_ = v___y_481_;
v___y_471_ = v___x_505_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_481_;
goto v___jp_459_;
}
else
{
v___y_460_ = v___y_498_;
v___y_461_ = v___y_478_;
v___y_462_ = v___x_499_;
v___y_463_ = v___y_479_;
v___y_464_ = v___x_504_;
v___y_465_ = v___y_482_;
v___y_466_ = v___y_475_;
v___y_467_ = v___x_508_;
v___y_468_ = v___y_480_;
v___y_469_ = v___x_502_;
v___y_470_ = v___y_481_;
v___y_471_ = v___x_505_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_478_;
goto v___jp_459_;
}
}
v___jp_513_:
{
lean_object* v___x_526_; lean_object* v_env_527_; lean_object* v_nextMacroScope_528_; lean_object* v_ngen_529_; lean_object* v_auxDeclNGen_530_; lean_object* v_traceState_531_; lean_object* v_recordedDeps_532_; lean_object* v_messages_533_; lean_object* v_infoState_534_; lean_object* v_snapshotTasks_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_559_; 
v___x_526_ = lean_st_ref_take(v___y_517_);
v_env_527_ = lean_ctor_get(v___x_526_, 0);
v_nextMacroScope_528_ = lean_ctor_get(v___x_526_, 1);
v_ngen_529_ = lean_ctor_get(v___x_526_, 2);
v_auxDeclNGen_530_ = lean_ctor_get(v___x_526_, 3);
v_traceState_531_ = lean_ctor_get(v___x_526_, 4);
v_recordedDeps_532_ = lean_ctor_get(v___x_526_, 6);
v_messages_533_ = lean_ctor_get(v___x_526_, 7);
v_infoState_534_ = lean_ctor_get(v___x_526_, 8);
v_snapshotTasks_535_ = lean_ctor_get(v___x_526_, 9);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_526_, 5);
lean_dec(v_unused_560_);
v___x_537_ = v___x_526_;
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_snapshotTasks_535_);
lean_inc(v_infoState_534_);
lean_inc(v_messages_533_);
lean_inc(v_recordedDeps_532_);
lean_inc(v_traceState_531_);
lean_inc(v_auxDeclNGen_530_);
lean_inc(v_ngen_529_);
lean_inc(v_nextMacroScope_528_);
lean_inc(v_env_527_);
lean_dec(v___x_526_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_Kernel_enableDiag(v_env_527_, v___y_519_);
lean_inc_ref(v___y_520_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 5, v___y_520_);
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_nextMacroScope_528_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_ngen_529_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_auxDeclNGen_530_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_traceState_531_);
lean_ctor_set(v_reuseFailAlloc_558_, 5, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 6, v_recordedDeps_532_);
lean_ctor_set(v_reuseFailAlloc_558_, 7, v_messages_533_);
lean_ctor_set(v_reuseFailAlloc_558_, 8, v_infoState_534_);
lean_ctor_set(v_reuseFailAlloc_558_, 9, v_snapshotTasks_535_);
v___x_541_ = v_reuseFailAlloc_558_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v_toCold_543_; lean_object* v_currRecDepth_544_; lean_object* v_ref_545_; uint8_t v_suppressElabErrors_546_; uint8_t v_isRecordingDeps_547_; lean_object* v_fileName_548_; lean_object* v_fileMap_549_; lean_object* v_currNamespace_550_; lean_object* v_openDecls_551_; lean_object* v_initHeartbeats_552_; lean_object* v_maxHeartbeats_553_; lean_object* v_quotContext_554_; lean_object* v_currMacroScope_555_; lean_object* v_cancelTk_x3f_556_; lean_object* v_inheritedTraceOptions_557_; 
v___x_542_ = lean_st_ref_put(v___y_517_, v___x_541_);
v_toCold_543_ = lean_ctor_get(v___y_524_, 0);
lean_inc_ref(v_toCold_543_);
v_currRecDepth_544_ = lean_ctor_get(v___y_524_, 1);
lean_inc(v_currRecDepth_544_);
v_ref_545_ = lean_ctor_get(v___y_524_, 2);
lean_inc(v_ref_545_);
v_suppressElabErrors_546_ = lean_ctor_get_uint8(v___y_524_, sizeof(void*)*3 + 2);
v_isRecordingDeps_547_ = lean_ctor_get_uint8(v___y_524_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_524_);
v_fileName_548_ = lean_ctor_get(v_toCold_543_, 0);
lean_inc_ref(v_fileName_548_);
v_fileMap_549_ = lean_ctor_get(v_toCold_543_, 1);
lean_inc_ref(v_fileMap_549_);
v_currNamespace_550_ = lean_ctor_get(v_toCold_543_, 4);
lean_inc(v_currNamespace_550_);
v_openDecls_551_ = lean_ctor_get(v_toCold_543_, 5);
lean_inc(v_openDecls_551_);
v_initHeartbeats_552_ = lean_ctor_get(v_toCold_543_, 6);
lean_inc(v_initHeartbeats_552_);
v_maxHeartbeats_553_ = lean_ctor_get(v_toCold_543_, 7);
lean_inc(v_maxHeartbeats_553_);
v_quotContext_554_ = lean_ctor_get(v_toCold_543_, 8);
lean_inc(v_quotContext_554_);
v_currMacroScope_555_ = lean_ctor_get(v_toCold_543_, 9);
lean_inc(v_currMacroScope_555_);
v_cancelTk_x3f_556_ = lean_ctor_get(v_toCold_543_, 10);
lean_inc(v_cancelTk_x3f_556_);
v_inheritedTraceOptions_557_ = lean_ctor_get(v_toCold_543_, 11);
lean_inc_ref(v_inheritedTraceOptions_557_);
lean_dec_ref(v_toCold_543_);
v___y_475_ = v___y_520_;
v___y_476_ = v___y_521_;
v___y_477_ = v___y_514_;
v___y_478_ = v___y_515_;
v___y_479_ = v___y_516_;
v___y_480_ = v___y_522_;
v___y_481_ = v___y_523_;
v___y_482_ = v___y_518_;
v___y_483_ = v___y_525_;
v_fileName_484_ = v_fileName_548_;
v_fileMap_485_ = v_fileMap_549_;
v_currNamespace_486_ = v_currNamespace_550_;
v_openDecls_487_ = v_openDecls_551_;
v_initHeartbeats_488_ = v_initHeartbeats_552_;
v_maxHeartbeats_489_ = v_maxHeartbeats_553_;
v_quotContext_490_ = v_quotContext_554_;
v_currMacroScope_491_ = v_currMacroScope_555_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_556_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_557_;
v_currRecDepth_494_ = v_currRecDepth_544_;
v_ref_495_ = v_ref_545_;
v_suppressElabErrors_496_ = v_suppressElabErrors_546_;
v_isRecordingDeps_497_ = v_isRecordingDeps_547_;
v___y_498_ = v___y_517_;
goto v___jp_474_;
}
}
}
v___jp_561_:
{
lean_object* v___x_570_; 
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc_ref(v___y_562_);
v___x_570_ = lean_infer_type(v___y_562_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_n(v_a_571_, 2);
lean_dec_ref_known(v___x_570_, 1);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_572_ = lean_apply_6(v_checkType_259_, v_a_571_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, lean_box(0));
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v_nextMacroScope_581_; lean_object* v_ngen_582_; lean_object* v_auxDeclNGen_583_; lean_object* v_traceState_584_; lean_object* v_recordedDeps_585_; lean_object* v_messages_586_; lean_object* v_infoState_587_; lean_object* v_snapshotTasks_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref_known(v___x_572_, 1);
v___x_573_ = lean_array_to_list(v___y_564_);
lean_inc_n(v___y_565_, 2);
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v___y_565_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_ctor_set(v___x_574_, 2, v_a_571_);
v___x_575_ = lean_box(0);
lean_inc(v___y_563_);
v___x_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_576_, 0, v___y_565_);
lean_ctor_set(v___x_576_, 1, v___y_563_);
v___x_577_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_577_, 0, v___x_574_);
lean_ctor_set(v___x_577_, 1, v___y_562_);
lean_ctor_set(v___x_577_, 2, v___x_575_);
lean_ctor_set(v___x_577_, 3, v___x_576_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*4, v_safety_260_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_st_ref_take(v___y_569_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
v_nextMacroScope_581_ = lean_ctor_get(v___x_579_, 1);
v_ngen_582_ = lean_ctor_get(v___x_579_, 2);
v_auxDeclNGen_583_ = lean_ctor_get(v___x_579_, 3);
v_traceState_584_ = lean_ctor_get(v___x_579_, 4);
v_recordedDeps_585_ = lean_ctor_get(v___x_579_, 6);
v_messages_586_ = lean_ctor_get(v___x_579_, 7);
v_infoState_587_ = lean_ctor_get(v___x_579_, 8);
v_snapshotTasks_588_ = lean_ctor_get(v___x_579_, 9);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_579_, 5);
lean_dec(v_unused_655_);
v___x_590_ = v___x_579_;
v_isShared_591_ = v_isSharedCheck_654_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snapshotTasks_588_);
lean_inc(v_infoState_587_);
lean_inc(v_messages_586_);
lean_inc(v_recordedDeps_585_);
lean_inc(v_traceState_584_);
lean_inc(v_auxDeclNGen_583_);
lean_inc(v_ngen_582_);
lean_inc(v_nextMacroScope_581_);
lean_inc(v_env_580_);
lean_dec(v___x_579_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_654_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc(v___y_565_);
v___x_592_ = l_Lean_markMeta(v_env_580_, v___y_565_);
v___x_593_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 5, v___x_593_);
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_nextMacroScope_581_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_ngen_582_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_auxDeclNGen_583_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_traceState_584_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_recordedDeps_585_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_messages_586_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v_infoState_587_);
lean_ctor_set(v_reuseFailAlloc_653_, 9, v_snapshotTasks_588_);
v___x_595_ = v_reuseFailAlloc_653_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_mctx_598_; lean_object* v_zetaDeltaFVarIds_599_; lean_object* v_postponed_600_; lean_object* v_diag_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_651_; 
v___x_596_ = lean_st_ref_put(v___y_569_, v___x_595_);
v___x_597_ = lean_st_ref_take(v___y_567_);
v_mctx_598_ = lean_ctor_get(v___x_597_, 0);
v_zetaDeltaFVarIds_599_ = lean_ctor_get(v___x_597_, 2);
v_postponed_600_ = lean_ctor_get(v___x_597_, 3);
v_diag_601_ = lean_ctor_get(v___x_597_, 4);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_597_, 1);
lean_dec(v_unused_652_);
v___x_603_ = v___x_597_;
v_isShared_604_ = v_isSharedCheck_651_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_diag_601_);
lean_inc(v_postponed_600_);
lean_inc(v_zetaDeltaFVarIds_599_);
lean_inc(v_mctx_598_);
lean_dec(v___x_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_651_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_mctx_598_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_zetaDeltaFVarIds_599_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_postponed_600_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_diag_601_);
v___x_607_ = v_reuseFailAlloc_650_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_env_610_; lean_object* v_checked_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_608_ = lean_st_ref_put(v___y_567_, v___x_607_);
v___x_609_ = lean_st_ref_get(v___y_569_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v_checked_611_ = lean_ctor_get(v_env_610_, 2);
lean_inc_ref(v_checked_611_);
lean_dec_ref(v_env_610_);
v___x_612_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_613_ = l_Lean_traceBlock___redArg(v___x_612_, v_checked_611_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_toCold_614_; lean_object* v_currRecDepth_615_; lean_object* v_ref_616_; uint8_t v_suppressElabErrors_617_; uint8_t v_isRecordingDeps_618_; lean_object* v_fileName_619_; lean_object* v_fileMap_620_; lean_object* v_options_621_; lean_object* v_currNamespace_622_; lean_object* v_openDecls_623_; lean_object* v_initHeartbeats_624_; lean_object* v_maxHeartbeats_625_; lean_object* v_quotContext_626_; lean_object* v_currMacroScope_627_; lean_object* v_cancelTk_x3f_628_; lean_object* v_inheritedTraceOptions_629_; uint8_t v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint16_t v___x_634_; lean_object* v___x_635_; lean_object* v_env_636_; uint8_t v___x_637_; uint16_t v___x_638_; uint16_t v___x_639_; uint16_t v___x_640_; uint8_t v___x_641_; 
lean_dec_ref_known(v___x_613_, 1);
v_toCold_614_ = lean_ctor_get(v___y_568_, 0);
v_currRecDepth_615_ = lean_ctor_get(v___y_568_, 1);
v_ref_616_ = lean_ctor_get(v___y_568_, 2);
v_suppressElabErrors_617_ = lean_ctor_get_uint8(v___y_568_, sizeof(void*)*3 + 2);
v_isRecordingDeps_618_ = lean_ctor_get_uint8(v___y_568_, sizeof(void*)*3 + 3);
v_fileName_619_ = lean_ctor_get(v_toCold_614_, 0);
v_fileMap_620_ = lean_ctor_get(v_toCold_614_, 1);
v_options_621_ = lean_ctor_get(v_toCold_614_, 2);
v_currNamespace_622_ = lean_ctor_get(v_toCold_614_, 4);
v_openDecls_623_ = lean_ctor_get(v_toCold_614_, 5);
v_initHeartbeats_624_ = lean_ctor_get(v_toCold_614_, 6);
v_maxHeartbeats_625_ = lean_ctor_get(v_toCold_614_, 7);
v_quotContext_626_ = lean_ctor_get(v_toCold_614_, 8);
v_currMacroScope_627_ = lean_ctor_get(v_toCold_614_, 9);
v_cancelTk_x3f_628_ = lean_ctor_get(v_toCold_614_, 10);
v_inheritedTraceOptions_629_ = lean_ctor_get(v_toCold_614_, 11);
v___x_630_ = 1;
v___x_631_ = 0;
v___x_632_ = l_Lean_Elab_async;
lean_inc_ref(v_options_621_);
v___x_633_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_621_, v___x_632_, v___x_631_);
v___x_634_ = l_Lean_OptionFlags_ofOptions(v___x_633_);
v___x_635_ = lean_st_ref_get(v___y_569_);
v_env_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_635_);
v___x_637_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_636_);
lean_dec_ref(v_env_636_);
v___x_638_ = 512;
v___x_639_ = lean_uint16_land(v___x_634_, v___x_638_);
v___x_640_ = 0;
v___x_641_ = lean_uint16_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
if (v___x_637_ == 0)
{
v___y_514_ = v___x_633_;
v___y_515_ = v___x_631_;
v___y_516_ = v___y_566_;
v___y_517_ = v___y_569_;
v___y_518_ = v___x_578_;
v___y_519_ = v___x_630_;
v___y_520_ = v___x_593_;
v___y_521_ = v___x_634_;
v___y_522_ = v___y_565_;
v___y_523_ = v___x_630_;
v___y_524_ = v___y_568_;
v___y_525_ = v___y_567_;
goto v___jp_513_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_629_);
lean_inc(v_cancelTk_x3f_628_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc_ref(v_fileMap_620_);
lean_inc_ref(v_fileName_619_);
lean_inc(v_ref_616_);
lean_inc(v_currRecDepth_615_);
lean_dec_ref(v___y_568_);
v___y_475_ = v___x_593_;
v___y_476_ = v___x_634_;
v___y_477_ = v___x_633_;
v___y_478_ = v___x_631_;
v___y_479_ = v___y_566_;
v___y_480_ = v___y_565_;
v___y_481_ = v___x_630_;
v___y_482_ = v___x_578_;
v___y_483_ = v___y_567_;
v_fileName_484_ = v_fileName_619_;
v_fileMap_485_ = v_fileMap_620_;
v_currNamespace_486_ = v_currNamespace_622_;
v_openDecls_487_ = v_openDecls_623_;
v_initHeartbeats_488_ = v_initHeartbeats_624_;
v_maxHeartbeats_489_ = v_maxHeartbeats_625_;
v_quotContext_490_ = v_quotContext_626_;
v_currMacroScope_491_ = v_currMacroScope_627_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_628_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_629_;
v_currRecDepth_494_ = v_currRecDepth_615_;
v_ref_495_ = v_ref_616_;
v_suppressElabErrors_496_ = v_suppressElabErrors_617_;
v_isRecordingDeps_497_ = v_isRecordingDeps_618_;
v___y_498_ = v___y_569_;
goto v___jp_474_;
}
}
else
{
if (v___x_637_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_629_);
lean_inc(v_cancelTk_x3f_628_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc_ref(v_fileMap_620_);
lean_inc_ref(v_fileName_619_);
lean_inc(v_ref_616_);
lean_inc(v_currRecDepth_615_);
lean_dec_ref(v___y_568_);
v___y_475_ = v___x_593_;
v___y_476_ = v___x_634_;
v___y_477_ = v___x_633_;
v___y_478_ = v___x_631_;
v___y_479_ = v___y_566_;
v___y_480_ = v___y_565_;
v___y_481_ = v___x_630_;
v___y_482_ = v___x_578_;
v___y_483_ = v___y_567_;
v_fileName_484_ = v_fileName_619_;
v_fileMap_485_ = v_fileMap_620_;
v_currNamespace_486_ = v_currNamespace_622_;
v_openDecls_487_ = v_openDecls_623_;
v_initHeartbeats_488_ = v_initHeartbeats_624_;
v_maxHeartbeats_489_ = v_maxHeartbeats_625_;
v_quotContext_490_ = v_quotContext_626_;
v_currMacroScope_491_ = v_currMacroScope_627_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_628_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_629_;
v_currRecDepth_494_ = v_currRecDepth_615_;
v_ref_495_ = v_ref_616_;
v_suppressElabErrors_496_ = v_suppressElabErrors_617_;
v_isRecordingDeps_497_ = v_isRecordingDeps_618_;
v___y_498_ = v___y_569_;
goto v___jp_474_;
}
else
{
v___y_514_ = v___x_633_;
v___y_515_ = v___x_631_;
v___y_516_ = v___y_566_;
v___y_517_ = v___y_569_;
v___y_518_ = v___x_578_;
v___y_519_ = v___x_631_;
v___y_520_ = v___x_593_;
v___y_521_ = v___x_634_;
v___y_522_ = v___y_565_;
v___y_523_ = v___x_630_;
v___y_524_ = v___y_568_;
v___y_525_ = v___y_567_;
goto v___jp_513_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref_known(v___x_578_, 1);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
v_a_642_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_613_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_613_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
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
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_a_571_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_562_);
v_a_656_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_572_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_572_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_checkType_259_);
v_a_664_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_570_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_570_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
v___jp_672_:
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_st_ref_get(v___y_265_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_676_ = l_Lean_Core_mkFreshUserName(v___x_675_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_mkPrivateName(v_env_674_, v_a_677_);
lean_dec_ref(v_env_674_);
v___x_679_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_261_, v___y_263_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_params_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_n(v_a_680_, 2);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_682_ = l_Lean_collectLevelParams(v___x_681_, v_a_680_);
v_params_683_ = lean_ctor_get(v___x_682_, 2);
lean_inc_ref(v_params_683_);
lean_dec_ref(v___x_682_);
v___x_684_ = lean_box(0);
v___x_685_ = l_Lean_Expr_hasMVar(v_a_680_);
if (v___x_685_ == 0)
{
v___y_562_ = v_a_680_;
v___y_563_ = v___x_684_;
v___y_564_ = v_params_683_;
v___y_565_ = v___x_678_;
v___y_566_ = v___y_262_;
v___y_567_ = v___y_263_;
v___y_568_ = v___y_264_;
v___y_569_ = v___y_265_;
goto v___jp_561_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_680_);
v___x_687_ = l_Lean_indentExpr(v_a_680_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_688_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec_ref_known(v___x_689_, 1);
v___y_562_ = v_a_680_;
v___y_563_ = v___x_684_;
v___y_564_ = v_params_683_;
v___y_565_ = v___x_678_;
v___y_566_ = v___y_262_;
v___y_567_ = v___y_263_;
v___y_568_ = v___y_264_;
v___y_569_ = v___y_265_;
goto v___jp_561_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_params_683_);
lean_dec(v_a_680_);
lean_dec(v___x_678_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_checkType_259_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v___x_678_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_checkType_259_);
v_a_698_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_679_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_679_);
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
lean_dec_ref(v_env_674_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_value_261_);
lean_dec_ref(v_checkType_259_);
v_a_706_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_676_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_676_);
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
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_mctx_728_; lean_object* v_zetaDeltaFVarIds_729_; lean_object* v_postponed_730_; lean_object* v_diag_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_740_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_725_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_725_, 0, v___y_723_);
lean_ctor_set(v___x_725_, 1, v_nextMacroScope_715_);
lean_ctor_set(v___x_725_, 2, v_ngen_716_);
lean_ctor_set(v___x_725_, 3, v_auxDeclNGen_717_);
lean_ctor_set(v___x_725_, 4, v_traceState_718_);
lean_ctor_set(v___x_725_, 5, v___x_724_);
lean_ctor_set(v___x_725_, 6, v_recordedDeps_719_);
lean_ctor_set(v___x_725_, 7, v_messages_720_);
lean_ctor_set(v___x_725_, 8, v_infoState_721_);
lean_ctor_set(v___x_725_, 9, v_snapshotTasks_722_);
v___x_726_ = lean_st_ref_put(v___y_265_, v___x_725_);
v___x_727_ = lean_st_ref_take(v___y_263_);
v_mctx_728_ = lean_ctor_get(v___x_727_, 0);
v_zetaDeltaFVarIds_729_ = lean_ctor_get(v___x_727_, 2);
v_postponed_730_ = lean_ctor_get(v___x_727_, 3);
v_diag_731_ = lean_ctor_get(v___x_727_, 4);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_727_, 1);
lean_dec(v_unused_741_);
v___x_733_ = v___x_727_;
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_diag_731_);
lean_inc(v_postponed_730_);
lean_inc(v_zetaDeltaFVarIds_729_);
lean_inc(v_mctx_728_);
lean_dec(v___x_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_mctx_728_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_zetaDeltaFVarIds_729_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_postponed_730_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_diag_731_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = lean_st_ref_put(v___y_263_, v___x_737_);
goto v___jp_672_;
}
}
}
v___jp_743_:
{
lean_object* v___x_744_; lean_object* v_env_745_; lean_object* v_nextMacroScope_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_traceState_749_; lean_object* v_recordedDeps_750_; lean_object* v_messages_751_; lean_object* v_infoState_752_; lean_object* v_snapshotTasks_753_; lean_object* v___x_754_; 
v___x_744_ = lean_st_ref_take(v___y_265_);
v_env_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref_n(v_env_745_, 2);
v_nextMacroScope_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_nextMacroScope_746_);
v_ngen_747_ = lean_ctor_get(v___x_744_, 2);
lean_inc_ref(v_ngen_747_);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_744_, 3);
lean_inc_ref(v_auxDeclNGen_748_);
v_traceState_749_ = lean_ctor_get(v___x_744_, 4);
lean_inc_ref(v_traceState_749_);
v_recordedDeps_750_ = lean_ctor_get(v___x_744_, 6);
lean_inc_ref(v_recordedDeps_750_);
v_messages_751_ = lean_ctor_get(v___x_744_, 7);
lean_inc_ref(v_messages_751_);
v_infoState_752_ = lean_ctor_get(v___x_744_, 8);
lean_inc_ref(v_infoState_752_);
v_snapshotTasks_753_ = lean_ctor_get(v___x_744_, 9);
lean_inc_ref(v_snapshotTasks_753_);
lean_dec(v___x_744_);
v___x_754_ = l_Lean_Environment_importEnv_x3f(v_env_745_);
if (lean_obj_tag(v___x_754_) == 0)
{
v_nextMacroScope_715_ = v_nextMacroScope_746_;
v_ngen_716_ = v_ngen_747_;
v_auxDeclNGen_717_ = v_auxDeclNGen_748_;
v_traceState_718_ = v_traceState_749_;
v_recordedDeps_719_ = v_recordedDeps_750_;
v_messages_720_ = v_messages_751_;
v_infoState_721_ = v_infoState_752_;
v_snapshotTasks_722_ = v_snapshotTasks_753_;
v___y_723_ = v_env_745_;
goto v___jp_714_;
}
else
{
lean_object* v_val_755_; 
lean_dec_ref(v_env_745_);
v_val_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v___x_754_, 1);
v_nextMacroScope_715_ = v_nextMacroScope_746_;
v_ngen_716_ = v_ngen_747_;
v_auxDeclNGen_717_ = v_auxDeclNGen_748_;
v_traceState_718_ = v_traceState_749_;
v_recordedDeps_719_ = v_recordedDeps_750_;
v_messages_720_ = v_messages_751_;
v_infoState_721_ = v_infoState_752_;
v_snapshotTasks_722_ = v_snapshotTasks_753_;
v___y_723_ = v_val_755_;
goto v___jp_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_764_, lean_object* v_checkType_765_, lean_object* v_safety_766_, lean_object* v_value_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_checkMeta_boxed_773_; uint8_t v_safety_boxed_774_; lean_object* v_res_775_; 
v_checkMeta_boxed_773_ = lean_unbox(v_checkMeta_764_);
v_safety_boxed_774_ = lean_unbox(v_safety_766_);
v_res_775_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_773_, v_checkType_765_, v_safety_boxed_774_, v_value_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(lean_object* v_env_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_nextMacroScope_781_; lean_object* v_ngen_782_; lean_object* v_auxDeclNGen_783_; lean_object* v_traceState_784_; lean_object* v_recordedDeps_785_; lean_object* v_messages_786_; lean_object* v_infoState_787_; lean_object* v_snapshotTasks_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_814_; 
v___x_780_ = lean_st_ref_take(v___y_778_);
v_nextMacroScope_781_ = lean_ctor_get(v___x_780_, 1);
v_ngen_782_ = lean_ctor_get(v___x_780_, 2);
v_auxDeclNGen_783_ = lean_ctor_get(v___x_780_, 3);
v_traceState_784_ = lean_ctor_get(v___x_780_, 4);
v_recordedDeps_785_ = lean_ctor_get(v___x_780_, 6);
v_messages_786_ = lean_ctor_get(v___x_780_, 7);
v_infoState_787_ = lean_ctor_get(v___x_780_, 8);
v_snapshotTasks_788_ = lean_ctor_get(v___x_780_, 9);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; 
v_unused_815_ = lean_ctor_get(v___x_780_, 5);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v___x_780_, 0);
lean_dec(v_unused_816_);
v___x_790_ = v___x_780_;
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snapshotTasks_788_);
lean_inc(v_infoState_787_);
lean_inc(v_messages_786_);
lean_inc(v_recordedDeps_785_);
lean_inc(v_traceState_784_);
lean_inc(v_auxDeclNGen_783_);
lean_inc(v_ngen_782_);
lean_inc(v_nextMacroScope_781_);
lean_dec(v___x_780_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 5, v___x_792_);
lean_ctor_set(v___x_790_, 0, v_env_776_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_env_776_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_nextMacroScope_781_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_ngen_782_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_auxDeclNGen_783_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_traceState_784_);
lean_ctor_set(v_reuseFailAlloc_813_, 5, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_813_, 6, v_recordedDeps_785_);
lean_ctor_set(v_reuseFailAlloc_813_, 7, v_messages_786_);
lean_ctor_set(v_reuseFailAlloc_813_, 8, v_infoState_787_);
lean_ctor_set(v_reuseFailAlloc_813_, 9, v_snapshotTasks_788_);
v___x_794_ = v_reuseFailAlloc_813_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_mctx_797_; lean_object* v_zetaDeltaFVarIds_798_; lean_object* v_postponed_799_; lean_object* v_diag_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_811_; 
v___x_795_ = lean_st_ref_put(v___y_778_, v___x_794_);
v___x_796_ = lean_st_ref_take(v___y_777_);
v_mctx_797_ = lean_ctor_get(v___x_796_, 0);
v_zetaDeltaFVarIds_798_ = lean_ctor_get(v___x_796_, 2);
v_postponed_799_ = lean_ctor_get(v___x_796_, 3);
v_diag_800_ = lean_ctor_get(v___x_796_, 4);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_796_, 1);
lean_dec(v_unused_812_);
v___x_802_ = v___x_796_;
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_diag_800_);
lean_inc(v_postponed_799_);
lean_inc(v_zetaDeltaFVarIds_798_);
lean_inc(v_mctx_797_);
lean_dec(v___x_796_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_mctx_797_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_zetaDeltaFVarIds_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_postponed_799_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_diag_800_);
v___x_807_ = v_reuseFailAlloc_810_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_st_ref_put(v___y_777_, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg___boxed(lean_object* v_env_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(lean_object* v_env_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; lean_object* v_env_830_; lean_object* v_a_832_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_829_ = lean_st_ref_get(v___y_827_);
v_env_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc_ref(v_env_830_);
lean_dec(v___x_829_);
v___x_842_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_822_, v___y_825_, v___y_827_);
lean_dec_ref(v___x_842_);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
v___x_843_ = lean_apply_5(v_x_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, lean_box(0));
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_830_, v___y_825_, v___y_827_);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_853_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_a_844_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_844_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_843_, 1);
v_a_832_ = v_a_854_;
goto v___jp_831_;
}
v___jp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v___x_833_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_830_, v___y_825_, v___y_827_);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_841_);
v___x_835_ = v___x_833_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_dec(v___x_833_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 1);
lean_ctor_set(v___x_835_, 0, v_a_832_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_832_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg___boxed(lean_object* v_env_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_855_, v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_863_, lean_object* v_checkType_864_, uint8_t v_safety_865_, uint8_t v_checkMeta_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v_env_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_872_ = lean_box(v_checkMeta_866_);
v___x_873_ = lean_box(v_safety_865_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_874_, 0, v___x_872_);
lean_closure_set(v___f_874_, 1, v_checkType_864_);
lean_closure_set(v___f_874_, 2, v___x_873_);
lean_closure_set(v___f_874_, 3, v_value_863_);
v___x_875_ = lean_st_ref_get(v_a_870_);
v_env_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc_ref(v_env_876_);
lean_dec(v___x_875_);
v___x_877_ = l_Lean_Environment_unlockAsync(v_env_876_);
v___x_878_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v___x_877_, v___f_874_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_879_, lean_object* v_checkType_880_, lean_object* v_safety_881_, lean_object* v_checkMeta_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
uint8_t v_safety_boxed_888_; uint8_t v_checkMeta_boxed_889_; lean_object* v_res_890_; 
v_safety_boxed_888_ = lean_unbox(v_safety_881_);
v_checkMeta_boxed_889_ = lean_unbox(v_checkMeta_882_);
v_res_890_ = l_Lean_Meta_evalExprCore___redArg(v_value_879_, v_checkType_880_, v_safety_boxed_888_, v_checkMeta_boxed_889_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_891_, lean_object* v_value_892_, lean_object* v_checkType_893_, uint8_t v_safety_894_, uint8_t v_checkMeta_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Meta_evalExprCore___redArg(v_value_892_, v_checkType_893_, v_safety_894_, v_checkMeta_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_902_, lean_object* v_value_903_, lean_object* v_checkType_904_, lean_object* v_safety_905_, lean_object* v_checkMeta_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_safety_boxed_912_; uint8_t v_checkMeta_boxed_913_; lean_object* v_res_914_; 
v_safety_boxed_912_ = lean_unbox(v_safety_905_);
v_checkMeta_boxed_913_ = lean_unbox(v_checkMeta_906_);
v_res_914_ = l_Lean_Meta_evalExprCore(v_00_u03b1_902_, v_value_903_, v_checkType_904_, v_safety_boxed_912_, v_checkMeta_boxed_913_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_00_u03b1_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_00_u03b1_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_00_u03b1_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_00_u03b1_929_, lean_object* v_constName_930_, uint8_t v_checkMeta_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_930_, v_checkMeta_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_00_u03b1_938_, lean_object* v_constName_939_, lean_object* v_checkMeta_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v_checkMeta_boxed_946_; lean_object* v_res_947_; 
v_checkMeta_boxed_946_ = lean_unbox(v_checkMeta_940_);
v_res_947_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(v_00_u03b1_938_, v_constName_939_, v_checkMeta_boxed_946_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_948_, lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_msg_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_956_, lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_956_, v_msg_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(lean_object* v_env_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___redArg(v_env_964_, v___y_966_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10___boxed(lean_object* v_env_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6_spec__10(v_env_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v_00_u03b1_978_, lean_object* v_env_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___redArg(v_env_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v_00_u03b1_987_, lean_object* v_env_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__6(v_00_u03b1_987_, v_env_988_, v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object* v_00_u03b1_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(v_00_u03b1_1004_, v_x_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1015_, lean_object* v_type_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Meta_whnfD(v_type_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1036_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_Expr_isConstOf(v_a_1023_, v_typeName_1015_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_del_object(v___x_1025_);
v___x_1028_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1029_ = l_Lean_indentExpr(v_a_1023_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1030_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_dec(v_a_1023_);
v___x_1032_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1032_);
v___x_1034_ = v___x_1025_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1022_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1022_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1045_, lean_object* v_type_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1045_, v_type_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_typeName_1045_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1053_, lean_object* v_value_1054_, uint8_t v_safety_1055_, uint8_t v_checkMeta_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1062_, 0, v_typeName_1053_);
v___x_1063_ = l_Lean_Meta_evalExprCore___redArg(v_value_1054_, v___f_1062_, v_safety_1055_, v_checkMeta_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1064_, lean_object* v_value_1065_, lean_object* v_safety_1066_, lean_object* v_checkMeta_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
uint8_t v_safety_boxed_1073_; uint8_t v_checkMeta_boxed_1074_; lean_object* v_res_1075_; 
v_safety_boxed_1073_ = lean_unbox(v_safety_1066_);
v_checkMeta_boxed_1074_ = lean_unbox(v_checkMeta_1067_);
v_res_1075_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1064_, v_value_1065_, v_safety_boxed_1073_, v_checkMeta_boxed_1074_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1076_, lean_object* v_typeName_1077_, lean_object* v_value_1078_, uint8_t v_safety_1079_, uint8_t v_checkMeta_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1077_, v_value_1078_, v_safety_1079_, v_checkMeta_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_typeName_1088_, lean_object* v_value_1089_, lean_object* v_safety_1090_, lean_object* v_checkMeta_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
uint8_t v_safety_boxed_1097_; uint8_t v_checkMeta_boxed_1098_; lean_object* v_res_1099_; 
v_safety_boxed_1097_ = lean_unbox(v_safety_1090_);
v_checkMeta_boxed_1098_ = lean_unbox(v_checkMeta_1091_);
v_res_1099_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1087_, v_typeName_1088_, v_value_1089_, v_safety_boxed_1097_, v_checkMeta_boxed_1098_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1105_, lean_object* v_type_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
lean_inc_ref(v_expectedType_1105_);
lean_inc_ref(v_type_1106_);
v___x_1112_ = l_Lean_Meta_isExprDefEq(v_type_1106_, v_expectedType_1105_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1137_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_unbox(v_a_1113_);
lean_dec(v_a_1113_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1115_);
v___x_1118_ = lean_box(0);
v___x_1119_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1120_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1106_, v_expectedType_1105_, v___x_1118_, v___x_1119_, v___y_1107_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_a_1121_);
v___x_1124_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___x_1123_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1124_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1120_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1120_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec_ref(v_type_1106_);
lean_dec_ref(v_expectedType_1105_);
v___x_1133_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1133_);
v___x_1135_ = v___x_1115_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_type_1106_);
lean_dec_ref(v_expectedType_1105_);
v_a_1138_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1112_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1112_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1146_, lean_object* v_type_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1146_, v_type_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1154_, lean_object* v_value_1155_, uint8_t v_safety_1156_, uint8_t v_checkMeta_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1163_, 0, v_expectedType_1154_);
v___x_1164_ = l_Lean_Meta_evalExprCore___redArg(v_value_1155_, v___f_1163_, v_safety_1156_, v_checkMeta_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1165_, lean_object* v_value_1166_, lean_object* v_safety_1167_, lean_object* v_checkMeta_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
uint8_t v_safety_boxed_1174_; uint8_t v_checkMeta_boxed_1175_; lean_object* v_res_1176_; 
v_safety_boxed_1174_ = lean_unbox(v_safety_1167_);
v_checkMeta_boxed_1175_ = lean_unbox(v_checkMeta_1168_);
v_res_1176_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1165_, v_value_1166_, v_safety_boxed_1174_, v_checkMeta_boxed_1175_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1177_, lean_object* v_expectedType_1178_, lean_object* v_value_1179_, uint8_t v_safety_1180_, uint8_t v_checkMeta_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1178_, v_value_1179_, v_safety_1180_, v_checkMeta_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_expectedType_1189_, lean_object* v_value_1190_, lean_object* v_safety_1191_, lean_object* v_checkMeta_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_safety_boxed_1198_; uint8_t v_checkMeta_boxed_1199_; lean_object* v_res_1200_; 
v_safety_boxed_1198_ = lean_unbox(v_safety_1191_);
v_checkMeta_boxed_1199_ = lean_unbox(v_checkMeta_1192_);
v_res_1200_ = l_Lean_Meta_evalExpr(v_00_u03b1_1188_, v_expectedType_1189_, v_value_1190_, v_safety_boxed_1198_, v_checkMeta_boxed_1199_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1200_;
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

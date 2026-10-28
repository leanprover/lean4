// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: public import Lean.PrettyPrinter.Delaborator.Options public import Lean.Compiler.LCNF.Internalize import Init.Data.Format.Macro
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_pp_funBinderTypes;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_letVarTypes;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_String_quote(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_explicit;
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
uint8_t l_Lean_Expr_isType0(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
extern lean_object* l_Lean_pp_all;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_pp_sanitizeNames;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___boxed(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2;
static const lean_array_object l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctor_"};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo = (const lean_object*)&l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " # "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "oproj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "uproj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sproj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pap "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reset["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "box "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unbox "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isShared "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@&"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "let "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fun "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "jp "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goto "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " =>"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "| _ =>"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cases "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "return "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = "⊥ : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "oset "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "] := "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "uset "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sset "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "] : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setTag "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__28 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__29 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inc["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__30 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__31 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inc"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__32 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "[ref]"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__34 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[persistent]"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__35 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dec["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__37 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__38 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__39 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " objs]"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__40 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "del "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__41 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__42 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "def "};
static const lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object* v_f_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_Format_indentD(v_f_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object* v_f_6_, lean_object* v_a_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_array_15_; lean_object* v_start_16_; lean_object* v_stop_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_35_; 
v_array_15_ = lean_ctor_get(v_a_7_, 0);
v_start_16_ = lean_ctor_get(v_a_7_, 1);
v_stop_17_ = lean_ctor_get(v_a_7_, 2);
v_isSharedCheck_35_ = !lean_is_exclusive(v_a_7_);
if (v_isSharedCheck_35_ == 0)
{
v___x_19_ = v_a_7_;
v_isShared_20_ = v_isSharedCheck_35_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_stop_17_);
lean_inc(v_start_16_);
lean_inc(v_array_15_);
lean_dec(v_a_7_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_35_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_lt(v_start_16_, v_stop_17_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_del_object(v___x_19_);
lean_dec(v_stop_17_);
lean_dec(v_start_16_);
lean_dec_ref(v_array_15_);
lean_dec_ref(v_f_6_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_b_8_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_start_16_, v___x_23_);
lean_inc_ref(v_array_15_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_24_);
v___x_26_ = v___x_19_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_array_15_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v_stop_17_);
v___x_26_ = v_reuseFailAlloc_34_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_array_fget(v_array_15_, v_start_16_);
lean_dec(v_start_16_);
lean_dec_ref(v_array_15_);
lean_inc_ref(v_f_6_);
lean_inc(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc_ref(v___y_9_);
v___x_28_ = lean_apply_7(v_f_6_, v___x_27_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_28_, 1);
v___x_30_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_31_, 0, v_b_8_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_a_29_);
v_a_7_ = v___x_26_;
v_b_8_ = v___x_32_;
goto _start;
}
else
{
lean_dec_ref(v___x_26_);
lean_dec(v_b_8_);
lean_dec_ref(v_f_6_);
return v___x_28_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object* v_f_36_, lean_object* v_a_37_, lean_object* v_b_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_36_, v_a_37_, v_b_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object* v_as_46_, lean_object* v_f_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_array_get_size(v_as_46_);
v___x_56_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref(v_f_47_);
lean_dec_ref(v_as_46_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_array_fget_borrowed(v_as_46_, v___x_54_);
lean_inc_ref(v_f_47_);
lean_inc(v_a_52_);
lean_inc_ref(v_a_51_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc_ref(v_a_48_);
lean_inc(v___x_59_);
v___x_60_ = lean_apply_7(v_f_47_, v___x_59_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, lean_box(0));
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = l_Array_toSubarray___redArg(v_as_46_, v___x_62_, v___x_55_);
v___x_64_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_47_, v___x_63_, v_a_61_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
return v___x_64_;
}
else
{
lean_dec_ref(v_f_47_);
lean_dec_ref(v_as_46_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(lean_object* v_as_65_, lean_object* v_f_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(v_as_65_, v_f_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object* v_00_u03b1_74_, lean_object* v_as_75_, lean_object* v_f_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(v_as_75_, v_f_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(lean_object* v_00_u03b1_84_, lean_object* v_as_85_, lean_object* v_f_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(v_00_u03b1_84_, v_as_85_, v_f_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object* v_00_u03b1_94_, lean_object* v_f_95_, lean_object* v_inst_96_, lean_object* v_R_97_, lean_object* v_a_98_, lean_object* v_b_99_, lean_object* v_c_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_95_, v_a_98_, v_b_99_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_f_109_, lean_object* v_inst_110_, lean_object* v_R_111_, lean_object* v_a_112_, lean_object* v_b_113_, lean_object* v_c_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(v_00_u03b1_108_, v_f_109_, v_inst_110_, v_R_111_, v_a_112_, v_b_113_, v_c_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object* v_f_122_, lean_object* v_pre_123_, lean_object* v_as_124_, size_t v_sz_125_, size_t v_i_126_, lean_object* v_b_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_lt(v_i_126_, v_sz_125_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec(v_pre_123_);
lean_dec_ref(v_f_122_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_b_127_);
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_136_ = lean_array_uget_borrowed(v_as_124_, v_i_126_);
lean_inc_ref(v_f_122_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc_ref(v___y_128_);
lean_inc(v_a_136_);
v___x_137_ = lean_apply_7(v_f_122_, v_a_136_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; size_t v___x_141_; size_t v___x_142_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
lean_inc(v_pre_123_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v_b_127_);
lean_ctor_set(v___x_139_, 1, v_pre_123_);
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_138_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_add(v_i_126_, v___x_141_);
v_i_126_ = v___x_142_;
v_b_127_ = v___x_140_;
goto _start;
}
else
{
lean_dec(v_b_127_);
lean_dec(v_pre_123_);
lean_dec_ref(v_f_122_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object* v_f_144_, lean_object* v_pre_145_, lean_object* v_as_146_, lean_object* v_sz_147_, lean_object* v_i_148_, lean_object* v_b_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_147_);
lean_dec(v_sz_147_);
v_i_boxed_157_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_144_, v_pre_145_, v_as_146_, v_sz_boxed_156_, v_i_boxed_157_, v_b_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec_ref(v_as_146_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object* v_pre_159_, lean_object* v_as_160_, lean_object* v_f_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_result_168_; size_t v_sz_169_; size_t v___x_170_; lean_object* v___x_171_; 
v_result_168_ = lean_box(0);
v_sz_169_ = lean_array_size(v_as_160_);
v___x_170_ = ((size_t)0ULL);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_161_, v_pre_159_, v_as_160_, v_sz_169_, v___x_170_, v_result_168_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object* v_pre_172_, lean_object* v_as_173_, lean_object* v_f_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v_pre_172_, v_as_173_, v_f_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec_ref(v_as_173_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object* v_00_u03b1_182_, lean_object* v_pre_183_, lean_object* v_as_184_, lean_object* v_f_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v_pre_183_, v_as_184_, v_f_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object* v_00_u03b1_193_, lean_object* v_pre_194_, lean_object* v_as_195_, lean_object* v_f_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(v_00_u03b1_193_, v_pre_194_, v_as_195_, v_f_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec_ref(v_as_195_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object* v_00_u03b1_204_, lean_object* v_f_205_, lean_object* v_pre_206_, lean_object* v_as_207_, size_t v_sz_208_, size_t v_i_209_, lean_object* v_b_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_205_, v_pre_206_, v_as_207_, v_sz_208_, v_i_209_, v_b_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object* v_00_u03b1_218_, lean_object* v_f_219_, lean_object* v_pre_220_, lean_object* v_as_221_, lean_object* v_sz_222_, lean_object* v_i_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
size_t v_sz_boxed_231_; size_t v_i_boxed_232_; lean_object* v_res_233_; 
v_sz_boxed_231_ = lean_unbox_usize(v_sz_222_);
lean_dec(v_sz_222_);
v_i_boxed_232_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(v_00_u03b1_218_, v_f_219_, v_pre_220_, v_as_221_, v_sz_boxed_231_, v_i_boxed_232_, v_b_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec_ref(v_as_221_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object* v_fvarId_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
lean_inc(v_fvarId_234_);
v___x_240_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_fvarId_234_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_251_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = 1;
v___x_246_ = l_Lean_Name_toString(v_a_241_, v___x_245_);
v___x_247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_270_; 
v_a_252_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_270_ == 0)
{
v___x_254_ = v___x_240_;
v_isShared_255_ = v_isSharedCheck_270_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_240_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_270_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = l_Lean_Exception_isInterrupt(v_a_252_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
lean_inc(v_a_252_);
v___x_257_ = l_Lean_Exception_isRuntime(v_a_252_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_a_252_);
v___x_258_ = 1;
v___x_259_ = l_Lean_Name_toString(v_fvarId_234_, v___x_258_);
v___x_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 0);
lean_ctor_set(v___x_254_, 0, v___x_260_);
v___x_262_ = v___x_254_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v_fvarId_234_);
if (v_isShared_255_ == 0)
{
v___x_265_ = v___x_254_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_252_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v_fvarId_234_);
if (v_isShared_255_ == 0)
{
v___x_268_ = v___x_254_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_252_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object* v_fvarId_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* v_fvarId_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_278_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* v_fvarId_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Compiler_LCNF_PP_ppFVar(v_fvarId_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__1);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg();
return v_res_300_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_307_; uint64_t v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2(void){
_start:
{
uint64_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_uint64_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1);
v___x_310_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set_uint64(v___x_311_, sizeof(void*)*1, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_317_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_317_);
lean_ctor_set(v___x_319_, 5, v___x_317_);
lean_ctor_set(v___x_319_, 6, v___x_317_);
lean_ctor_set(v___x_319_, 7, v___x_317_);
lean_ctor_set(v___x_319_, 8, v___x_317_);
lean_ctor_set(v___x_319_, 9, v___x_317_);
lean_ctor_set(v___x_319_, 10, v___x_317_);
lean_ctor_set(v___x_319_, 11, v___x_316_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg();
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_322_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
v___x_323_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_321_);
lean_ctor_set(v___x_323_, 3, v___x_321_);
lean_ctor_set(v___x_323_, 4, v___x_321_);
lean_ctor_set(v___x_323_, 5, v___x_321_);
lean_ctor_set(v___x_323_, 6, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(32u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9(void){
_start:
{
size_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = ((size_t)5ULL);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_unsigned_to_nat(32u);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
v___x_331_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
v___x_332_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_328_);
lean_ctor_set(v___x_332_, 3, v___x_328_);
lean_ctor_set_usize(v___x_332_, 4, v___x_327_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
lean_ctor_set(v___x_334_, 4, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10);
v___x_336_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
v___x_337_ = lean_box(1);
v___x_338_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
lean_ctor_set(v___x_340_, 2, v___x_337_);
lean_ctor_set(v___x_340_, 3, v___x_336_);
lean_ctor_set(v___x_340_, 4, v___x_335_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* v_e_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_346_ = lean_box(1);
v___x_347_ = 0;
v___x_348_ = 1;
v___x_349_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3));
v___x_352_ = lean_box(0);
lean_inc_ref(v_a_342_);
v___x_353_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v___x_346_);
lean_ctor_set(v___x_353_, 2, v_a_342_);
lean_ctor_set(v___x_353_, 3, v___x_351_);
lean_ctor_set(v___x_353_, 4, v___x_352_);
lean_ctor_set(v___x_353_, 5, v___x_350_);
lean_ctor_set(v___x_353_, 6, v___x_352_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7, v___x_347_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 1, v___x_347_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 2, v___x_347_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 3, v___x_348_);
v___x_354_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11);
v___x_355_ = lean_st_mk_ref(v___x_354_);
v___x_356_ = l_Lean_Meta_ppExpr(v_e_341_, v___x_353_, v___x_355_, v_a_343_, v_a_344_);
lean_dec_ref_known(v___x_353_, 7);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_st_ref_get(v___x_355_);
lean_dec(v___x_355_);
lean_dec(v___x_361_);
if (v_isShared_360_ == 0)
{
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_357_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_dec(v___x_355_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* v_e_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_372_, v_a_373_, v_a_376_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0(lean_object* v_00_u03b2_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg___boxed(lean_object* v___dummy_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0(lean_object* v_00_u03b2_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* v_opts_396_, lean_object* v_opt_397_){
_start:
{
lean_object* v_name_398_; lean_object* v_defValue_399_; lean_object* v_map_400_; lean_object* v___x_401_; 
v_name_398_ = lean_ctor_get(v_opt_397_, 0);
v_defValue_399_ = lean_ctor_get(v_opt_397_, 1);
v_map_400_ = lean_ctor_get(v_opts_396_, 0);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_400_, v_name_398_);
if (lean_obj_tag(v___x_401_) == 0)
{
uint8_t v___x_402_; 
v___x_402_ = lean_unbox(v_defValue_399_);
return v___x_402_;
}
else
{
lean_object* v_val_403_; 
v_val_403_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_401_, 1);
if (lean_obj_tag(v_val_403_) == 1)
{
uint8_t v_v_404_; 
v_v_404_ = lean_ctor_get_uint8(v_val_403_, 0);
lean_dec_ref_known(v_val_403_, 0);
return v_v_404_;
}
else
{
uint8_t v___x_405_; 
lean_dec(v_val_403_);
v___x_405_ = lean_unbox(v_defValue_399_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* v_opts_406_, lean_object* v_opt_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_406_, v_opt_407_);
lean_dec_ref(v_opt_407_);
lean_dec_ref(v_opts_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_nat_to_int(v_a_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
v___x_421_ = lean_string_length(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
v___x_423_ = lean_nat_to_int(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
switch(lean_obj_tag(v_e_428_))
{
case 0:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
case 1:
{
lean_object* v_fvarId_437_; lean_object* v___x_438_; 
v_fvarId_437_ = lean_ctor_get(v_e_428_, 0);
lean_inc(v_fvarId_437_);
lean_dec_ref_known(v_e_428_, 1);
v___x_438_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_437_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_438_;
}
default: 
{
lean_object* v_expr_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_475_; 
v_expr_439_ = lean_ctor_get(v_e_428_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_e_428_);
if (v_isSharedCheck_475_ == 0)
{
v___x_441_ = v_e_428_;
v_isShared_442_ = v_isSharedCheck_475_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_expr_439_);
lean_dec(v_e_428_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_475_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_432_);
v___x_444_ = l_Lean_pp_explicit;
v___x_445_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_443_, v___x_444_);
lean_dec_ref(v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec_ref(v_expr_439_);
v___x_446_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 0);
lean_ctor_set(v___x_441_, 0, v___x_446_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
uint8_t v___x_450_; 
lean_del_object(v___x_441_);
v___x_450_ = l_Lean_Expr_isConst(v_expr_439_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Expr_isProp(v_expr_439_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Expr_isType0(v_expr_439_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
v___x_453_ = l_Lean_Expr_isFVar(v_expr_439_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_439_, v_a_429_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_470_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_470_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_470_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_470_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_459_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_460_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_a_455_);
v___x_462_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_459_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_466_);
v___x_468_ = v___x_457_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
return v___x_454_;
}
}
else
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_439_, v_a_429_, v_a_432_, v_a_433_);
return v___x_471_;
}
}
else
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_439_, v_a_429_, v_a_432_, v_a_433_);
return v___x_472_;
}
}
else
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_439_, v_a_429_, v_a_432_, v_a_433_);
return v___x_473_;
}
}
else
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_439_, v_a_429_, v_a_432_, v_a_433_);
return v___x_474_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* v_e_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t v_pu_484_, lean_object* v_e_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* v_pu_493_, lean_object* v_e_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
uint8_t v_pu_boxed_501_; lean_object* v_res_502_; 
v_pu_boxed_501_ = lean_unbox(v_pu_493_);
v_res_502_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_boxed_501_, v_e_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t v_pu_503_, lean_object* v_args_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_512_ = lean_box(v_pu_503_);
v___x_513_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(v___x_513_, 0, v___x_512_);
v___x_514_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_511_, v_args_504_, v___x_513_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* v_pu_515_, lean_object* v_args_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
uint8_t v_pu_boxed_523_; lean_object* v_res_524_; 
v_pu_boxed_523_ = lean_unbox(v_pu_515_);
v_res_524_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_boxed_523_, v_args_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_args_516_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* v_lit_525_){
_start:
{
uint64_t v_v_528_; 
switch(lean_obj_tag(v_lit_525_))
{
case 0:
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
v_val_533_ = lean_ctor_get(v_lit_525_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_lit_525_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v_lit_525_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_lit_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Nat_reprFast(v_val_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 3);
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
}
case 1:
{
lean_object* v_val_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_552_; 
v_val_543_ = lean_ctor_get(v_lit_525_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_lit_525_);
if (v_isSharedCheck_552_ == 0)
{
v___x_545_ = v_lit_525_;
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_val_543_);
lean_dec(v_lit_525_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_String_quote(v_val_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 3);
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
case 2:
{
uint8_t v_val_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_val_553_ = lean_ctor_get_uint8(v_lit_525_, 0);
lean_dec_ref_known(v_lit_525_, 0);
v___x_554_ = lean_uint8_to_nat(v_val_553_);
v___x_555_ = l_Nat_reprFast(v___x_554_);
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
case 3:
{
uint16_t v_val_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_val_558_ = lean_ctor_get_uint16(v_lit_525_, 0);
lean_dec_ref_known(v_lit_525_, 0);
v___x_559_ = lean_uint16_to_nat(v_val_558_);
v___x_560_ = l_Nat_reprFast(v___x_559_);
v___x_561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
case 4:
{
uint32_t v_val_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_val_563_ = lean_ctor_get_uint32(v_lit_525_, 0);
lean_dec_ref_known(v_lit_525_, 0);
v___x_564_ = lean_uint32_to_nat(v_val_563_);
v___x_565_ = l_Nat_reprFast(v___x_564_);
v___x_566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
default: 
{
uint64_t v_val_568_; 
v_val_568_ = lean_ctor_get_uint64(v_lit_525_, 0);
lean_dec_ref(v_lit_525_);
v_v_528_ = v_val_568_;
goto v___jp_527_;
}
}
v___jp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_529_ = lean_uint64_to_nat(v_v_528_);
v___x_530_ = l_Nat_reprFast(v___x_529_);
v___x_531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* v_lit_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* v_lit_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_572_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* v_lit_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* v_x_600_){
_start:
{
lean_object* v_name_601_; lean_object* v_cidx_602_; lean_object* v_usize_603_; lean_object* v_ssize_604_; lean_object* v_r_606_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_r_620_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_name_601_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_name_601_);
v_cidx_602_ = lean_ctor_get(v_x_600_, 1);
lean_inc(v_cidx_602_);
v_usize_603_ = lean_ctor_get(v_x_600_, 3);
lean_inc(v_usize_603_);
v_ssize_604_ = lean_ctor_get(v_x_600_, 4);
lean_inc(v_ssize_604_);
lean_dec_ref(v_x_600_);
v___x_617_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
v___x_618_ = l_Nat_reprFast(v_cidx_602_);
v___x_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v_r_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_620_, 0, v___x_617_);
lean_ctor_set(v_r_620_, 1, v___x_619_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v_usize_603_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_lt(v___x_631_, v_ssize_604_);
if (v___x_633_ == 0)
{
lean_dec(v_ssize_604_);
lean_dec(v_usize_603_);
v_r_606_ = v_r_620_;
goto v___jp_605_;
}
else
{
goto v___jp_621_;
}
}
else
{
goto v___jp_621_;
}
v___jp_605_:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_name_eq(v_name_601_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_r_616_; 
v___x_609_ = 1;
v___x_610_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v_r_606_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_Name_toString(v_name_601_, v___x_609_);
v___x_613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v_r_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_616_, 0, v___x_614_);
lean_ctor_set(v_r_616_, 1, v___x_615_);
return v_r_616_;
}
else
{
lean_dec(v_name_601_);
return v_r_606_;
}
}
v___jp_621_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_r_630_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v_r_620_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Nat_reprFast(v_usize_603_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_623_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_622_);
v___x_628_ = l_Nat_reprFast(v_ssize_604_);
v___x_629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v_r_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_630_, 0, v___x_627_);
lean_ctor_set(v_r_630_, 1, v___x_629_);
v_r_606_ = v_r_630_;
goto v___jp_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_683_, lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
switch(lean_obj_tag(v_e_684_))
{
case 0:
{
lean_object* v_value_691_; lean_object* v___x_692_; 
v_value_691_ = lean_ctor_get(v_e_684_, 0);
lean_inc_ref(v_value_691_);
lean_dec_ref_known(v_e_684_, 1);
v___x_692_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_691_);
return v___x_692_;
}
case 1:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
case 2:
{
lean_object* v_idx_695_; lean_object* v_struct_696_; lean_object* v___x_697_; 
v_idx_695_ = lean_ctor_get(v_e_684_, 1);
lean_inc(v_idx_695_);
v_struct_696_ = lean_ctor_get(v_e_684_, 2);
lean_inc(v_struct_696_);
lean_dec_ref_known(v_e_684_, 3);
v___x_697_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_696_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_710_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_710_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_710_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_710_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_702_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v_a_698_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Nat_reprFast(v_idx_695_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_703_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_706_);
v___x_708_ = v___x_700_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_dec(v_idx_695_);
return v___x_697_;
}
}
case 3:
{
lean_object* v_declName_711_; lean_object* v_us_712_; lean_object* v_args_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_declName_711_ = lean_ctor_get(v_e_684_, 0);
lean_inc(v_declName_711_);
v_us_712_ = lean_ctor_get(v_e_684_, 1);
lean_inc(v_us_712_);
v_args_713_ = lean_ctor_get(v_e_684_, 2);
lean_inc_ref(v_args_713_);
lean_dec_ref_known(v_e_684_, 3);
v___x_714_ = l_Lean_Expr_const___override(v_declName_711_, v_us_712_);
v___x_715_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_714_, v_a_685_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_713_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_713_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v_a_716_);
lean_ctor_set(v___x_722_, 1, v_a_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_dec(v_a_716_);
return v___x_717_;
}
}
else
{
lean_dec_ref(v_args_713_);
return v___x_715_;
}
}
case 4:
{
lean_object* v_fvarId_727_; lean_object* v_args_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_746_; 
v_fvarId_727_ = lean_ctor_get(v_e_684_, 0);
v_args_728_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_746_ == 0)
{
v___x_730_ = v_e_684_;
v_isShared_731_ = v_isSharedCheck_746_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_args_728_);
lean_inc(v_fvarId_727_);
lean_dec(v_e_684_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_746_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_727_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_728_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_728_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_745_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_745_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 5);
lean_ctor_set(v___x_730_, 1, v_a_735_);
lean_ctor_set(v___x_730_, 0, v_a_733_);
v___x_740_ = v___x_730_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_a_735_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_dec(v_a_733_);
lean_del_object(v___x_730_);
return v___x_734_;
}
}
else
{
lean_del_object(v___x_730_);
lean_dec_ref(v_args_728_);
return v___x_732_;
}
}
}
case 5:
{
lean_object* v_i_747_; lean_object* v_args_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_765_; 
v_i_747_ = lean_ctor_get(v_e_684_, 0);
v_args_748_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_765_ == 0)
{
v___x_750_ = v_e_684_;
v_isShared_751_ = v_isSharedCheck_765_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_args_748_);
lean_inc(v_i_747_);
lean_dec(v_e_684_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_765_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_748_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_748_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_747_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v_a_753_);
lean_ctor_set(v___x_750_, 0, v___x_757_);
v___x_759_ = v___x_750_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_753_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_759_);
v___x_761_ = v___x_755_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_del_object(v___x_750_);
lean_dec_ref(v_i_747_);
return v___x_752_;
}
}
}
case 6:
{
lean_object* v_i_766_; lean_object* v_var_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_789_; 
v_i_766_ = lean_ctor_get(v_e_684_, 0);
v_var_767_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_789_ == 0)
{
v___x_769_ = v_e_684_;
v_isShared_770_ = v_isSharedCheck_789_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_var_767_);
lean_inc(v_i_766_);
lean_dec(v_e_684_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_789_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_767_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_788_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_788_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_776_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_777_ = l_Nat_reprFast(v_i_766_);
v___x_778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 5);
lean_ctor_set(v___x_769_, 1, v___x_778_);
lean_ctor_set(v___x_769_, 0, v___x_776_);
v___x_780_ = v___x_769_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_787_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_781_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_783_);
v___x_785_ = v___x_774_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_del_object(v___x_769_);
lean_dec(v_i_766_);
return v___x_771_;
}
}
}
case 7:
{
lean_object* v_i_790_; lean_object* v_var_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_813_; 
v_i_790_ = lean_ctor_get(v_e_684_, 0);
v_var_791_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_813_ == 0)
{
v___x_793_ = v_e_684_;
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_var_791_);
lean_inc(v_i_790_);
lean_dec(v_e_684_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_791_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_812_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_812_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_800_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
v___x_801_ = l_Nat_reprFast(v_i_790_);
v___x_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 5);
lean_ctor_set(v___x_793_, 1, v___x_802_);
lean_ctor_set(v___x_793_, 0, v___x_800_);
v___x_804_ = v___x_793_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_802_);
v___x_804_ = v_reuseFailAlloc_811_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_805_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_a_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_807_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_del_object(v___x_793_);
lean_dec(v_i_790_);
return v___x_795_;
}
}
}
case 8:
{
lean_object* v_n_814_; lean_object* v_offset_815_; lean_object* v_var_816_; lean_object* v___x_817_; 
v_n_814_ = lean_ctor_get(v_e_684_, 0);
lean_inc(v_n_814_);
v_offset_815_ = lean_ctor_get(v_e_684_, 1);
lean_inc(v_offset_815_);
v_var_816_ = lean_ctor_get(v_e_684_, 2);
lean_inc(v_var_816_);
lean_dec_ref_known(v_e_684_, 3);
v___x_817_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_816_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_837_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_822_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_823_ = l_Nat_reprFast(v_n_814_);
v___x_824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_822_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Nat_reprFast(v_offset_815_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_827_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_833_);
v___x_835_ = v___x_820_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_dec(v_offset_815_);
lean_dec(v_n_814_);
return v___x_817_;
}
}
case 9:
{
lean_object* v_fn_838_; lean_object* v_args_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_858_; 
v_fn_838_ = lean_ctor_get(v_e_684_, 0);
v_args_839_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_858_ == 0)
{
v___x_841_ = v_e_684_;
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_args_839_);
lean_inc(v_fn_838_);
lean_dec(v_e_684_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_839_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_839_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_857_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_857_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_848_ = 1;
v___x_849_ = l_Lean_Name_toString(v_fn_838_, v___x_848_);
v___x_850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 5);
lean_ctor_set(v___x_841_, 1, v_a_844_);
lean_ctor_set(v___x_841_, 0, v___x_850_);
v___x_852_ = v___x_841_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_a_844_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_852_);
v___x_854_ = v___x_846_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_del_object(v___x_841_);
lean_dec(v_fn_838_);
return v___x_843_;
}
}
}
case 10:
{
lean_object* v_fn_859_; lean_object* v_args_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_881_; 
v_fn_859_ = lean_ctor_get(v_e_684_, 0);
v_args_860_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_881_ == 0)
{
v___x_862_ = v_e_684_;
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_args_860_);
lean_inc(v_fn_859_);
lean_dec(v_e_684_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_860_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_860_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_880_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_880_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_869_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_870_ = 1;
v___x_871_ = l_Lean_Name_toString(v_fn_859_, v___x_870_);
v___x_872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 5);
lean_ctor_set(v___x_862_, 1, v___x_872_);
lean_ctor_set(v___x_862_, 0, v___x_869_);
v___x_874_ = v___x_862_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_879_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_875_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_del_object(v___x_862_);
lean_dec(v_fn_859_);
return v___x_864_;
}
}
}
case 11:
{
lean_object* v_n_882_; lean_object* v_var_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_905_; 
v_n_882_ = lean_ctor_get(v_e_684_, 0);
v_var_883_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_905_ == 0)
{
v___x_885_ = v_e_684_;
v_isShared_886_ = v_isSharedCheck_905_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_var_883_);
lean_inc(v_n_882_);
lean_dec(v_e_684_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_905_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_883_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_904_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_904_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_904_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_904_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_892_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_893_ = l_Nat_reprFast(v_n_882_);
v___x_894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 5);
lean_ctor_set(v___x_885_, 1, v___x_894_);
lean_ctor_set(v___x_885_, 0, v___x_892_);
v___x_896_ = v___x_885_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_903_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_897_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_899_);
v___x_901_ = v___x_890_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_del_object(v___x_885_);
lean_dec(v_n_882_);
return v___x_887_;
}
}
}
case 12:
{
lean_object* v_var_906_; lean_object* v_i_907_; uint8_t v_updateHeader_908_; lean_object* v_args_909_; lean_object* v___x_910_; 
v_var_906_ = lean_ctor_get(v_e_684_, 0);
lean_inc(v_var_906_);
v_i_907_ = lean_ctor_get(v_e_684_, 1);
lean_inc_ref(v_i_907_);
v_updateHeader_908_ = lean_ctor_get_uint8(v_e_684_, sizeof(void*)*3);
v_args_909_ = lean_ctor_get(v_e_684_, 2);
lean_inc_ref(v_args_909_);
lean_dec_ref_known(v_e_684_, 3);
v___x_910_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_906_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_683_, v_args_909_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_args_909_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_934_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_934_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_934_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_934_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___y_919_; 
v___x_917_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_908_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_919_ = v___x_932_;
goto v___jp_918_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_919_ = v___x_933_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
lean_inc(v___y_919_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_917_);
lean_ctor_set(v___x_920_, 1, v___y_919_);
v___x_921_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_a_911_);
v___x_923_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_907_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_913_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_920_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_928_);
v___x_930_ = v___x_915_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_dec(v_a_911_);
lean_dec_ref(v_i_907_);
return v___x_912_;
}
}
else
{
lean_dec_ref(v_args_909_);
lean_dec_ref(v_i_907_);
return v___x_910_;
}
}
case 13:
{
lean_object* v_fvarId_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_952_; 
v_fvarId_935_ = lean_ctor_get(v_e_684_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_e_684_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_e_684_, 0);
lean_dec(v_unused_953_);
v___x_937_ = v_e_684_;
v_isShared_938_ = v_isSharedCheck_952_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_fvarId_935_);
lean_dec(v_e_684_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_952_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_935_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 5);
lean_ctor_set(v___x_937_, 1, v_a_940_);
lean_ctor_set(v___x_937_, 0, v___x_944_);
v___x_946_ = v___x_937_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_a_940_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_946_);
v___x_948_ = v___x_942_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_del_object(v___x_937_);
return v___x_939_;
}
}
}
case 14:
{
lean_object* v_fvarId_954_; lean_object* v___x_955_; 
v_fvarId_954_ = lean_ctor_get(v_e_684_, 0);
lean_inc(v_fvarId_954_);
lean_dec_ref_known(v_e_684_, 1);
v___x_955_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_954_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
return v___x_955_;
}
}
default: 
{
lean_object* v_fvarId_966_; lean_object* v___x_967_; 
v_fvarId_966_ = lean_ctor_get(v_e_684_, 0);
lean_inc(v_fvarId_966_);
lean_dec_ref_known(v_e_684_, 1);
v___x_967_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_966_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_a_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_978_, lean_object* v_e_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_pu_boxed_986_; lean_object* v_res_987_; 
v_pu_boxed_986_ = lean_unbox(v_pu_978_);
v_res_987_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_986_, v_e_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_binderName_997_; lean_object* v_type_998_; uint8_t v_borrow_999_; lean_object* v___y_1001_; 
v_binderName_997_ = lean_ctor_get(v_param_992_, 1);
lean_inc(v_binderName_997_);
v_type_998_ = lean_ctor_get(v_param_992_, 2);
lean_inc_ref(v_type_998_);
v_borrow_999_ = lean_ctor_get_uint8(v_param_992_, sizeof(void*)*3);
lean_dec_ref(v_param_992_);
if (v_borrow_999_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1001_ = v___x_1034_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_1001_ = v___x_1035_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_994_);
v___x_1003_ = l_Lean_pp_funBinderTypes;
v___x_1004_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1002_, v___x_1003_);
lean_dec_ref(v___x_1002_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref(v_type_998_);
v___x_1005_ = 1;
v___x_1006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_997_, v___x_1005_);
lean_inc_ref(v___y_1001_);
v___x_1007_ = lean_string_append(v___y_1001_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_998_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1033_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1015_ = l_Lean_Name_toString(v_binderName_997_, v___x_1004_);
v___x_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc_ref(v___y_1001_);
v___x_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___y_1001_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v_a_1011_);
v___x_1022_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1023_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1021_);
v___x_1025_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1022_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = 0;
v___x_1029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*1, v___x_1028_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1029_);
v___x_1031_ = v___x_1013_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_dec(v_binderName_997_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1042_, lean_object* v_param_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1043_, v_a_1044_, v_a_1047_, v_a_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1051_, lean_object* v_param_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
uint8_t v_pu_boxed_1059_; lean_object* v_res_1060_; 
v_pu_boxed_1059_ = lean_unbox(v_pu_1051_);
v_res_1060_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1059_, v_param_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1061_, lean_object* v_params_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1070_ = lean_box(v_pu_1061_);
v___x_1071_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1069_, v_params_1062_, v___x_1071_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1073_, lean_object* v_params_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_pu_boxed_1081_; lean_object* v_res_1082_; 
v_pu_boxed_1081_ = lean_unbox(v_pu_1073_);
v_res_1082_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1081_, v_params_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec_ref(v_params_1074_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1089_, lean_object* v_letDecl_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1094_);
v___x_1098_ = l_Lean_pp_letVarTypes;
v___x_1099_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1097_, v___x_1098_);
lean_dec_ref(v___x_1097_);
if (v___x_1099_ == 0)
{
lean_object* v_binderName_1100_; lean_object* v_value_1101_; lean_object* v___x_1102_; 
v_binderName_1100_ = lean_ctor_get(v_letDecl_1090_, 1);
lean_inc(v_binderName_1100_);
v_value_1101_ = lean_ctor_get(v_letDecl_1090_, 3);
lean_inc(v_value_1101_);
lean_dec_ref(v_letDecl_1090_);
v___x_1102_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1089_, v_value_1101_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1118_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1118_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1118_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1107_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1108_ = 1;
v___x_1109_ = l_Lean_Name_toString(v_binderName_1100_, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1107_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1114_);
v___x_1116_ = v___x_1105_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_dec(v_binderName_1100_);
return v___x_1102_;
}
}
else
{
lean_object* v_binderName_1119_; lean_object* v_type_1120_; lean_object* v_value_1121_; lean_object* v___x_1122_; 
v_binderName_1119_ = lean_ctor_get(v_letDecl_1090_, 1);
lean_inc(v_binderName_1119_);
v_type_1120_ = lean_ctor_get(v_letDecl_1090_, 2);
lean_inc_ref(v_type_1120_);
v_value_1121_ = lean_ctor_get(v_letDecl_1090_, 3);
lean_inc(v_value_1121_);
lean_dec_ref(v_letDecl_1090_);
v___x_1122_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1120_, v_a_1091_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1148_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1148_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1148_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1089_, v_value_1121_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1147_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1147_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1147_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1133_ = l_Lean_Name_toString(v_binderName_1119_, v___x_1099_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 3);
lean_ctor_set(v___x_1125_, 0, v___x_1133_);
v___x_1135_ = v___x_1125_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1132_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_a_1123_);
v___x_1140_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1142_);
v___x_1144_ = v___x_1130_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_del_object(v___x_1125_);
lean_dec(v_a_1123_);
lean_dec(v_binderName_1119_);
return v___x_1127_;
}
}
}
else
{
lean_dec(v_value_1121_);
lean_dec(v_binderName_1119_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* v_pu_1149_, lean_object* v_letDecl_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v_pu_boxed_1157_; lean_object* v_res_1158_; 
v_pu_boxed_1157_ = lean_unbox(v_pu_1149_);
v_res_1158_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_boxed_1157_, v_letDecl_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_bs_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1162_ == 0)
{
return v_bs_1161_;
}
else
{
lean_object* v_v_1163_; lean_object* v_fvarId_1164_; lean_object* v___x_1165_; lean_object* v_bs_x27_1166_; lean_object* v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v_v_1163_ = lean_array_uget_borrowed(v_bs_1161_, v_i_1160_);
v_fvarId_1164_ = lean_ctor_get(v_v_1163_, 0);
lean_inc(v_fvarId_1164_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v_bs_x27_1166_ = lean_array_uset(v_bs_1161_, v_i_1160_, v___x_1165_);
v___x_1167_ = l_Lean_mkFVar(v_fvarId_1164_);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1160_, v___x_1168_);
v___x_1170_ = lean_array_uset(v_bs_x27_1166_, v_i_1160_, v___x_1167_);
v_i_1160_ = v___x_1169_;
v_bs_1161_ = v___x_1170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1172_, lean_object* v_i_1173_, lean_object* v_bs_1174_){
_start:
{
size_t v_sz_boxed_1175_; size_t v_i_boxed_1176_; lean_object* v_res_1177_; 
v_sz_boxed_1175_ = lean_unbox_usize(v_sz_1172_);
lean_dec(v_sz_1172_);
v_i_boxed_1176_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1175_, v_i_boxed_1176_, v_bs_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1178_, lean_object* v_ps_1179_, lean_object* v_type_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = l_Lean_Expr_isErased(v_type_1180_);
if (v___x_1184_ == 0)
{
if (v_pu_1178_ == 0)
{
size_t v_sz_1185_; size_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_sz_1185_ = lean_array_size(v_ps_1179_);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1185_, v___x_1186_, v_ps_1179_);
v___x_1188_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1180_, v___x_1187_, v_a_1181_, v_a_1182_);
lean_dec_ref(v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
lean_dec_ref(v_ps_1179_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_type_1180_);
return v___x_1189_;
}
}
else
{
lean_object* v___x_1190_; 
lean_dec_ref(v_ps_1179_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_type_1180_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1191_, lean_object* v_ps_1192_, lean_object* v_type_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
uint8_t v_pu_boxed_1197_; lean_object* v_res_1198_; 
v_pu_boxed_1197_ = lean_unbox(v_pu_1191_);
v_res_1198_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1197_, v_ps_1192_, v_type_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1223_, lean_object* v_alt_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
switch(lean_obj_tag(v_alt_1224_))
{
case 0:
{
lean_object* v_ctorName_1231_; lean_object* v_params_1232_; lean_object* v_code_1233_; lean_object* v___x_1234_; 
v_ctorName_1231_ = lean_ctor_get(v_alt_1224_, 0);
lean_inc(v_ctorName_1231_);
v_params_1232_ = lean_ctor_get(v_alt_1224_, 1);
lean_inc_ref(v_params_1232_);
v_code_1233_ = lean_ctor_get(v_alt_1224_, 2);
lean_inc_ref(v_code_1233_);
lean_dec_ref_known(v_alt_1224_, 3);
v___x_1234_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1223_, v_params_1232_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec_ref(v_params_1232_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1260_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1260_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1260_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1223_, v_code_1233_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1259_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1259_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1259_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1244_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1245_ = 1;
v___x_1246_ = l_Lean_Name_toString(v_ctorName_1231_, v___x_1245_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 3);
lean_ctor_set(v___x_1237_, 0, v___x_1246_);
v___x_1248_ = v___x_1237_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1244_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_a_1235_);
v___x_1251_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Std_Format_indentD(v_a_1240_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1254_);
v___x_1256_ = v___x_1242_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_del_object(v___x_1237_);
lean_dec(v_a_1235_);
lean_dec(v_ctorName_1231_);
return v___x_1239_;
}
}
}
else
{
lean_dec_ref(v_code_1233_);
lean_dec(v_ctorName_1231_);
return v___x_1234_;
}
}
case 1:
{
lean_object* v_info_1261_; lean_object* v_code_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1287_; 
v_info_1261_ = lean_ctor_get(v_alt_1224_, 0);
v_code_1262_ = lean_ctor_get(v_alt_1224_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_alt_1224_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1264_ = v_alt_1224_;
v_isShared_1265_ = v_isSharedCheck_1287_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_code_1262_);
lean_inc(v_info_1261_);
lean_dec(v_alt_1224_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1287_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1223_, v_code_1262_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1286_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1286_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1286_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_name_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v_name_1271_ = lean_ctor_get(v_info_1261_, 0);
lean_inc(v_name_1271_);
lean_dec_ref(v_info_1261_);
v___x_1272_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1273_ = 1;
v___x_1274_ = l_Lean_Name_toString(v_name_1271_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 5);
lean_ctor_set(v___x_1264_, 1, v___x_1275_);
lean_ctor_set(v___x_1264_, 0, v___x_1272_);
v___x_1277_ = v___x_1264_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Std_Format_indentD(v_a_1267_);
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1281_);
v___x_1283_ = v___x_1269_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_del_object(v___x_1264_);
lean_dec_ref(v_info_1261_);
return v___x_1266_;
}
}
}
default: 
{
lean_object* v_code_1288_; lean_object* v___x_1289_; 
v_code_1288_ = lean_ctor_get(v_alt_1224_, 0);
lean_inc_ref(v_code_1288_);
lean_dec_ref_known(v_alt_1224_, 1);
v___x_1289_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1223_, v_code_1288_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1300_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1300_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1300_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1294_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1295_ = l_Std_Format_indentD(v_a_1290_);
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1296_);
v___x_1298_ = v___x_1292_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1301_, lean_object* v_alt_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v_pu_boxed_1309_; lean_object* v_res_1310_; 
v_pu_boxed_1309_ = lean_unbox(v_pu_1301_);
v_res_1310_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1309_, v_alt_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1362_, lean_object* v_c_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
switch(lean_obj_tag(v_c_1363_))
{
case 0:
{
lean_object* v_decl_1370_; lean_object* v_k_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1393_; 
v_decl_1370_ = lean_ctor_get(v_c_1363_, 0);
v_k_1371_ = lean_ctor_get(v_c_1363_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1373_ = v_c_1363_;
v_isShared_1374_ = v_isSharedCheck_1393_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_k_1371_);
lean_inc(v_decl_1370_);
lean_dec(v_c_1363_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1393_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1362_, v_decl_1370_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1371_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1392_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1392_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1392_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 5);
lean_ctor_set(v___x_1373_, 1, v___x_1382_);
lean_ctor_set(v___x_1373_, 0, v_a_1376_);
v___x_1384_ = v___x_1373_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1376_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = lean_box(1);
v___x_1386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1387_);
v___x_1389_ = v___x_1380_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_dec(v_a_1376_);
lean_del_object(v___x_1373_);
return v___x_1377_;
}
}
else
{
lean_del_object(v___x_1373_);
lean_dec_ref(v_k_1371_);
return v___x_1375_;
}
}
}
case 1:
{
lean_object* v_decl_1394_; lean_object* v_k_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1419_; 
v_decl_1394_ = lean_ctor_get(v_c_1363_, 0);
v_k_1395_ = lean_ctor_get(v_c_1363_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1397_ = v_c_1363_;
v_isShared_1398_ = v_isSharedCheck_1419_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_k_1395_);
lean_inc(v_decl_1394_);
lean_dec(v_c_1363_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1419_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1362_, v_decl_1394_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1395_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1418_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 5);
lean_ctor_set(v___x_1397_, 1, v_a_1400_);
lean_ctor_set(v___x_1397_, 0, v___x_1406_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_a_1400_);
v___x_1408_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1409_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_box(1);
v___x_1412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_a_1402_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1413_);
v___x_1415_ = v___x_1404_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
else
{
lean_dec(v_a_1400_);
lean_del_object(v___x_1397_);
return v___x_1401_;
}
}
else
{
lean_del_object(v___x_1397_);
lean_dec_ref(v_k_1395_);
return v___x_1399_;
}
}
}
case 2:
{
lean_object* v_decl_1420_; lean_object* v_k_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1445_; 
v_decl_1420_ = lean_ctor_get(v_c_1363_, 0);
v_k_1421_ = lean_ctor_get(v_c_1363_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1423_ = v_c_1363_;
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_k_1421_);
lean_inc(v_decl_1420_);
lean_dec(v_c_1363_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1362_, v_decl_1420_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1421_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1444_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1444_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1444_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 5);
lean_ctor_set(v___x_1423_, 1, v_a_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1426_);
v___x_1434_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1435_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_box(1);
v___x_1438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1439_);
v___x_1441_ = v___x_1430_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_dec(v_a_1426_);
lean_del_object(v___x_1423_);
return v___x_1427_;
}
}
else
{
lean_del_object(v___x_1423_);
lean_dec_ref(v_k_1421_);
return v___x_1425_;
}
}
}
case 3:
{
lean_object* v_fvarId_1446_; lean_object* v_args_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1467_; 
v_fvarId_1446_ = lean_ctor_get(v_c_1363_, 0);
v_args_1447_ = lean_ctor_get(v_c_1363_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1449_ = v_c_1363_;
v_isShared_1450_ = v_isSharedCheck_1467_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_args_1447_);
lean_inc(v_fvarId_1446_);
lean_dec(v_c_1363_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1467_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1446_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1362_, v_args_1447_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec_ref(v_args_1447_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1466_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1466_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1466_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 5);
lean_ctor_set(v___x_1449_, 1, v_a_1452_);
lean_ctor_set(v___x_1449_, 0, v___x_1458_);
v___x_1460_ = v___x_1449_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_a_1452_);
v___x_1460_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1461_);
v___x_1463_ = v___x_1456_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_dec(v_a_1452_);
lean_del_object(v___x_1449_);
return v___x_1453_;
}
}
else
{
lean_del_object(v___x_1449_);
lean_dec_ref(v_args_1447_);
return v___x_1451_;
}
}
}
case 4:
{
lean_object* v_cases_1468_; lean_object* v_resultType_1469_; lean_object* v_discr_1470_; lean_object* v_alts_1471_; lean_object* v___x_1472_; 
v_cases_1468_ = lean_ctor_get(v_c_1363_, 0);
lean_inc_ref(v_cases_1468_);
lean_dec_ref_known(v_c_1363_, 1);
v_resultType_1469_ = lean_ctor_get(v_cases_1468_, 1);
lean_inc_ref(v_resultType_1469_);
v_discr_1470_ = lean_ctor_get(v_cases_1468_, 2);
lean_inc(v_discr_1470_);
v_alts_1471_ = lean_ctor_get(v_cases_1468_, 3);
lean_inc_ref(v_alts_1471_);
lean_dec_ref(v_cases_1468_);
v___x_1472_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1470_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1469_, v_a_1364_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = lean_box(1);
v___x_1477_ = lean_box(v_pu_1362_);
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1478_, 0, v___x_1477_);
v___x_1479_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1476_, v_alts_1471_, v___x_1478_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec_ref(v_alts_1471_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1493_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1484_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_a_1473_);
v___x_1486_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1475_);
v___x_1489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v_a_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1489_);
v___x_1491_ = v___x_1482_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_dec(v_a_1475_);
lean_dec(v_a_1473_);
return v___x_1479_;
}
}
else
{
lean_dec(v_a_1473_);
lean_dec_ref(v_alts_1471_);
return v___x_1474_;
}
}
else
{
lean_dec_ref(v_alts_1471_);
lean_dec_ref(v_resultType_1469_);
return v___x_1472_;
}
}
case 5:
{
lean_object* v_fvarId_1494_; lean_object* v___x_1495_; 
v_fvarId_1494_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1494_);
lean_dec_ref_known(v_c_1363_, 1);
v___x_1495_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1494_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
return v___x_1495_;
}
}
case 6:
{
lean_object* v_type_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1528_; 
v_type_1506_ = lean_ctor_get(v_c_1363_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1508_ = v_c_1363_;
v_isShared_1509_ = v_isSharedCheck_1528_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_type_1506_);
lean_dec(v_c_1363_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1528_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1367_);
v___x_1511_ = l_Lean_pp_all;
v___x_1512_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1510_, v___x_1511_);
lean_dec_ref(v___x_1510_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_dec_ref(v_type_1506_);
v___x_1513_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1513_);
v___x_1515_ = v___x_1508_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v___x_1517_; 
lean_del_object(v___x_1508_);
v___x_1517_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1506_, v_a_1364_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1527_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
return v___x_1517_;
}
}
}
}
case 7:
{
lean_object* v_fvarId_1529_; lean_object* v_i_1530_; lean_object* v_y_1531_; lean_object* v_k_1532_; lean_object* v___x_1533_; 
v_fvarId_1529_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1529_);
v_i_1530_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_i_1530_);
v_y_1531_ = lean_ctor_get(v_c_1363_, 2);
lean_inc(v_y_1531_);
v_k_1532_ = lean_ctor_get(v_c_1363_, 3);
lean_inc_ref(v_k_1532_);
lean_dec_ref_known(v_c_1363_, 4);
v___x_1533_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1529_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1531_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1566_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1566_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1566_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1532_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1565_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1565_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1565_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1545_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v_a_1534_);
v___x_1547_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Nat_reprFast(v_i_1530_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 3);
lean_ctor_set(v___x_1538_, 0, v___x_1549_);
v___x_1551_ = v___x_1538_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1548_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1536_);
v___x_1556_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_box(1);
v___x_1559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1560_);
v___x_1562_ = v___x_1543_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_del_object(v___x_1538_);
lean_dec(v_a_1536_);
lean_dec(v_a_1534_);
lean_dec(v_i_1530_);
return v___x_1540_;
}
}
}
else
{
lean_dec(v_a_1534_);
lean_dec_ref(v_k_1532_);
lean_dec(v_i_1530_);
return v___x_1535_;
}
}
else
{
lean_dec_ref(v_k_1532_);
lean_dec(v_y_1531_);
lean_dec(v_i_1530_);
return v___x_1533_;
}
}
case 8:
{
lean_object* v_fvarId_1567_; lean_object* v_i_1568_; lean_object* v_y_1569_; lean_object* v_k_1570_; lean_object* v___x_1571_; 
v_fvarId_1567_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1567_);
v_i_1568_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_i_1568_);
v_y_1569_ = lean_ctor_get(v_c_1363_, 2);
lean_inc(v_y_1569_);
v_k_1570_ = lean_ctor_get(v_c_1363_, 3);
lean_inc_ref(v_k_1570_);
lean_dec_ref_known(v_c_1363_, 4);
v___x_1571_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1567_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1569_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1604_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1604_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1604_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1570_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1603_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1583_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1572_);
v___x_1585_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Nat_reprFast(v_i_1568_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 3);
lean_ctor_set(v___x_1576_, 0, v___x_1587_);
v___x_1589_ = v___x_1576_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1586_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v_a_1574_);
v___x_1594_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_box(1);
v___x_1597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_a_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1598_);
v___x_1600_ = v___x_1581_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_del_object(v___x_1576_);
lean_dec(v_a_1574_);
lean_dec(v_a_1572_);
lean_dec(v_i_1568_);
return v___x_1578_;
}
}
}
else
{
lean_dec(v_a_1572_);
lean_dec_ref(v_k_1570_);
lean_dec(v_i_1568_);
return v___x_1573_;
}
}
else
{
lean_dec_ref(v_k_1570_);
lean_dec(v_y_1569_);
lean_dec(v_i_1568_);
return v___x_1571_;
}
}
case 9:
{
lean_object* v_fvarId_1605_; lean_object* v_i_1606_; lean_object* v_offset_1607_; lean_object* v_y_1608_; lean_object* v_ty_1609_; lean_object* v_k_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_fvarId_1605_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1605_);
v_i_1606_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_i_1606_);
v_offset_1607_ = lean_ctor_get(v_c_1363_, 2);
lean_inc(v_offset_1607_);
v_y_1608_ = lean_ctor_get(v_c_1363_, 3);
lean_inc(v_y_1608_);
v_ty_1609_ = lean_ctor_get(v_c_1363_, 4);
lean_inc_ref(v_ty_1609_);
v_k_1610_ = lean_ctor_get(v_c_1363_, 5);
lean_inc_ref(v_k_1610_);
lean_dec_ref_known(v_c_1363_, 6);
v___x_1611_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1367_);
v___x_1612_ = l_Lean_pp_letVarTypes;
v___x_1613_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1611_, v___x_1612_);
lean_dec_ref(v___x_1611_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v_ty_1609_);
v___x_1614_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1605_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1658_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1658_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1658_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1608_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1657_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1657_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1657_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1610_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1656_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1656_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1656_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1629_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1615_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Nat_reprFast(v_i_1606_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 3);
lean_ctor_set(v___x_1622_, 0, v___x_1633_);
v___x_1635_ = v___x_1622_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Nat_reprFast(v_offset_1607_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 3);
lean_ctor_set(v___x_1617_, 0, v___x_1639_);
v___x_1641_ = v___x_1617_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1638_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_a_1620_);
v___x_1646_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_box(1);
v___x_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_a_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1650_);
v___x_1652_ = v___x_1627_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_del_object(v___x_1622_);
lean_dec(v_a_1620_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1624_;
}
}
}
else
{
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
lean_dec_ref(v_k_1610_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1619_;
}
}
}
else
{
lean_dec_ref(v_k_1610_);
lean_dec(v_y_1608_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1614_;
}
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1605_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1609_, v_a_1364_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1708_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1708_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1708_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1608_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1707_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1707_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1707_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1610_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1706_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1706_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1706_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1676_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_a_1660_);
v___x_1678_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Nat_reprFast(v_i_1606_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 3);
lean_ctor_set(v___x_1669_, 0, v___x_1680_);
v___x_1682_ = v___x_1669_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1679_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Nat_reprFast(v_offset_1607_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 3);
lean_ctor_set(v___x_1664_, 0, v___x_1686_);
v___x_1688_ = v___x_1664_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1685_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_a_1662_);
v___x_1693_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_a_1667_);
v___x_1696_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_box(1);
v___x_1699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v_a_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1700_);
v___x_1702_ = v___x_1674_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
else
{
lean_del_object(v___x_1669_);
lean_dec(v_a_1667_);
lean_del_object(v___x_1664_);
lean_dec(v_a_1662_);
lean_dec(v_a_1660_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1671_;
}
}
}
else
{
lean_del_object(v___x_1664_);
lean_dec(v_a_1662_);
lean_dec(v_a_1660_);
lean_dec_ref(v_k_1610_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1666_;
}
}
}
else
{
lean_dec(v_a_1660_);
lean_dec_ref(v_k_1610_);
lean_dec(v_y_1608_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1661_;
}
}
else
{
lean_dec_ref(v_k_1610_);
lean_dec_ref(v_ty_1609_);
lean_dec(v_y_1608_);
lean_dec(v_offset_1607_);
lean_dec(v_i_1606_);
return v___x_1659_;
}
}
}
case 10:
{
lean_object* v_fvarId_1709_; lean_object* v_cidx_1710_; lean_object* v_k_1711_; lean_object* v___x_1712_; 
v_fvarId_1709_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1709_);
v_cidx_1710_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_cidx_1710_);
v_k_1711_ = lean_ctor_get(v_c_1363_, 2);
lean_inc_ref(v_k_1711_);
lean_dec_ref_known(v_c_1363_, 3);
v___x_1712_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1709_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1740_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1740_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1740_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1711_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1739_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1739_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1739_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1722_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v_a_1713_);
v___x_1724_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Nat_reprFast(v_cidx_1710_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 3);
lean_ctor_set(v___x_1715_, 0, v___x_1726_);
v___x_1728_ = v___x_1715_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1725_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_box(1);
v___x_1733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v_a_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1734_);
v___x_1736_ = v___x_1720_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_del_object(v___x_1715_);
lean_dec(v_a_1713_);
lean_dec(v_cidx_1710_);
return v___x_1717_;
}
}
}
else
{
lean_dec_ref(v_k_1711_);
lean_dec(v_cidx_1710_);
return v___x_1712_;
}
}
case 11:
{
lean_object* v_fvarId_1741_; lean_object* v_n_1742_; uint8_t v_check_1743_; uint8_t v_persistent_1744_; lean_object* v_k_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1814_; 
v_fvarId_1741_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1741_);
v_n_1742_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_n_1742_);
v_check_1743_ = lean_ctor_get_uint8(v_c_1363_, sizeof(void*)*3);
v_persistent_1744_ = lean_ctor_get_uint8(v_c_1363_, sizeof(void*)*3 + 1);
v_k_1745_ = lean_ctor_get(v_c_1363_, 2);
lean_inc_ref(v_k_1745_);
lean_dec_ref_known(v_c_1363_, 3);
if (v_persistent_1744_ == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1814_ = v___x_1817_;
goto v___jp_1813_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___y_1814_ = v___x_1818_;
goto v___jp_1813_;
}
v___jp_1746_:
{
lean_object* v_ann_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
lean_inc_ref(v___y_1747_);
v_ann_1749_ = lean_string_append(v___y_1747_, v___y_1748_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_dec_eq(v_n_1742_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1741_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1784_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1784_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1784_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1745_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1783_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1783_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1783_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1763_ = l_Nat_reprFast(v_n_1742_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 3);
lean_ctor_set(v___x_1755_, 0, v___x_1763_);
v___x_1765_ = v___x_1755_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1762_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_ann_1749_);
v___x_1770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v_a_1753_);
v___x_1774_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_box(1);
v___x_1777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1778_);
v___x_1780_ = v___x_1760_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_del_object(v___x_1755_);
lean_dec(v_a_1753_);
lean_dec_ref(v_ann_1749_);
lean_dec(v_n_1742_);
return v___x_1757_;
}
}
}
else
{
lean_dec_ref(v_ann_1749_);
lean_dec_ref(v_k_1745_);
lean_dec(v_n_1742_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1785_; 
lean_dec(v_n_1742_);
v___x_1785_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1741_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1812_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1812_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1812_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1745_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1811_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1811_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1811_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 3);
lean_ctor_set(v___x_1788_, 0, v_ann_1749_);
v___x_1797_ = v___x_1788_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_ann_1749_);
v___x_1797_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1795_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_a_1786_);
v___x_1802_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_box(1);
v___x_1805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_a_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1806_);
v___x_1808_ = v___x_1793_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_del_object(v___x_1788_);
lean_dec(v_a_1786_);
lean_dec_ref(v_ann_1749_);
return v___x_1790_;
}
}
}
else
{
lean_dec_ref(v_ann_1749_);
lean_dec_ref(v_k_1745_);
return v___x_1785_;
}
}
}
v___jp_1813_:
{
if (v_check_1743_ == 0)
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
v___y_1747_ = v___y_1814_;
v___y_1748_ = v___x_1815_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1747_ = v___y_1814_;
v___y_1748_ = v___x_1816_;
goto v___jp_1746_;
}
}
}
case 12:
{
lean_object* v_fvarId_1819_; lean_object* v_n_1820_; uint8_t v_check_1821_; uint8_t v_persistent_1822_; lean_object* v_objs_x3f_1823_; lean_object* v_k_1824_; lean_object* v_ann_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v_ann_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v_ann_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; 
v_fvarId_1819_ = lean_ctor_get(v_c_1363_, 0);
lean_inc(v_fvarId_1819_);
v_n_1820_ = lean_ctor_get(v_c_1363_, 1);
lean_inc(v_n_1820_);
v_check_1821_ = lean_ctor_get_uint8(v_c_1363_, sizeof(void*)*4);
v_persistent_1822_ = lean_ctor_get_uint8(v_c_1363_, sizeof(void*)*4 + 1);
v_objs_x3f_1823_ = lean_ctor_get(v_c_1363_, 2);
lean_inc(v_objs_x3f_1823_);
v_k_1824_ = lean_ctor_get(v_c_1363_, 3);
lean_inc_ref(v_k_1824_);
lean_dec_ref_known(v_c_1363_, 4);
if (v_persistent_1822_ == 0)
{
lean_object* v_ann_1918_; 
v_ann_1918_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v_ann_1910_ = v_ann_1918_;
v___y_1911_ = v_a_1364_;
v___y_1912_ = v_a_1365_;
v___y_1913_ = v_a_1366_;
v___y_1914_ = v_a_1367_;
v___y_1915_ = v_a_1368_;
goto v___jp_1909_;
}
else
{
lean_object* v_ann_1919_; 
v_ann_1919_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v_ann_1910_ = v_ann_1919_;
v___y_1911_ = v_a_1364_;
v___y_1912_ = v_a_1365_;
v___y_1913_ = v_a_1366_;
v___y_1914_ = v_a_1367_;
v___y_1915_ = v_a_1368_;
goto v___jp_1909_;
}
v___jp_1825_:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_dec_eq(v_n_1820_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1819_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1866_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1866_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1866_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1824_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1865_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1865_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1865_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1845_ = l_Nat_reprFast(v_n_1820_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 3);
lean_ctor_set(v___x_1837_, 0, v___x_1845_);
v___x_1847_ = v___x_1837_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1844_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_ann_1826_);
v___x_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_a_1835_);
v___x_1856_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_box(1);
v___x_1859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1860_);
v___x_1862_ = v___x_1842_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_del_object(v___x_1837_);
lean_dec(v_a_1835_);
lean_dec_ref(v_ann_1826_);
lean_dec(v_n_1820_);
return v___x_1839_;
}
}
}
else
{
lean_dec_ref(v_ann_1826_);
lean_dec_ref(v_k_1824_);
lean_dec(v_n_1820_);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1867_; 
lean_dec(v_n_1820_);
v___x_1867_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1819_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1894_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1894_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1894_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1824_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1893_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1893_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1893_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 3);
lean_ctor_set(v___x_1870_, 0, v_ann_1826_);
v___x_1879_ = v___x_1870_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_ann_1826_);
v___x_1879_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1877_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_a_1868_);
v___x_1884_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_box(1);
v___x_1887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_a_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1888_);
v___x_1890_ = v___x_1875_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_del_object(v___x_1870_);
lean_dec(v_a_1868_);
lean_dec_ref(v_ann_1826_);
return v___x_1872_;
}
}
}
else
{
lean_dec_ref(v_ann_1826_);
lean_dec_ref(v_k_1824_);
return v___x_1867_;
}
}
}
v___jp_1895_:
{
if (lean_obj_tag(v_objs_x3f_1823_) == 1)
{
lean_object* v_val_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_ann_1908_; 
v_val_1902_ = lean_ctor_get(v_objs_x3f_1823_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_objs_x3f_1823_, 1);
v___x_1903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0));
v___x_1904_ = l_Nat_reprFast(v_val_1902_);
v___x_1905_ = lean_string_append(v___x_1903_, v___x_1904_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__40));
v___x_1907_ = lean_string_append(v___x_1905_, v___x_1906_);
v_ann_1908_ = lean_string_append(v_ann_1896_, v___x_1907_);
lean_dec_ref(v___x_1907_);
v_ann_1826_ = v_ann_1908_;
v___y_1827_ = v___y_1897_;
v___y_1828_ = v___y_1898_;
v___y_1829_ = v___y_1899_;
v___y_1830_ = v___y_1900_;
v___y_1831_ = v___y_1901_;
goto v___jp_1825_;
}
else
{
lean_dec(v_objs_x3f_1823_);
v_ann_1826_ = v_ann_1896_;
v___y_1827_ = v___y_1897_;
v___y_1828_ = v___y_1898_;
v___y_1829_ = v___y_1899_;
v___y_1830_ = v___y_1900_;
v___y_1831_ = v___y_1901_;
goto v___jp_1825_;
}
}
v___jp_1909_:
{
if (v_check_1821_ == 0)
{
lean_object* v___x_1916_; lean_object* v_ann_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
lean_inc_ref(v_ann_1910_);
v_ann_1917_ = lean_string_append(v_ann_1910_, v___x_1916_);
v_ann_1896_ = v_ann_1917_;
v___y_1897_ = v___y_1911_;
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1913_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1915_;
goto v___jp_1895_;
}
else
{
lean_inc_ref(v_ann_1910_);
v_ann_1896_ = v_ann_1910_;
v___y_1897_ = v___y_1911_;
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1913_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1915_;
goto v___jp_1895_;
}
}
}
default: 
{
lean_object* v_fvarId_1920_; lean_object* v_k_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1945_; 
v_fvarId_1920_ = lean_ctor_get(v_c_1363_, 0);
v_k_1921_ = lean_ctor_get(v_c_1363_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_c_1363_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1923_ = v_c_1363_;
v_isShared_1924_ = v_isSharedCheck_1945_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_k_1921_);
lean_inc(v_fvarId_1920_);
lean_dec(v_c_1363_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1945_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1920_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1362_, v_k_1921_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1944_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1944_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1944_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__42));
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 5);
lean_ctor_set(v___x_1923_, 1, v_a_1926_);
lean_ctor_set(v___x_1923_, 0, v___x_1932_);
v___x_1934_ = v___x_1923_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_a_1926_);
v___x_1934_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_box(1);
v___x_1938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1939_);
v___x_1941_ = v___x_1930_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_dec(v_a_1926_);
lean_del_object(v___x_1923_);
return v___x_1927_;
}
}
else
{
lean_del_object(v___x_1923_);
lean_dec_ref(v_k_1921_);
return v___x_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1946_, lean_object* v_funDecl_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_binderName_1954_; lean_object* v_params_1955_; lean_object* v_type_1956_; lean_object* v_value_1957_; lean_object* v___x_1958_; 
v_binderName_1954_ = lean_ctor_get(v_funDecl_1947_, 1);
lean_inc(v_binderName_1954_);
v_params_1955_ = lean_ctor_get(v_funDecl_1947_, 2);
lean_inc_ref(v_params_1955_);
v_type_1956_ = lean_ctor_get(v_funDecl_1947_, 3);
lean_inc_ref(v_type_1956_);
v_value_1957_ = lean_ctor_get(v_funDecl_1947_, 4);
lean_inc_ref(v_value_1957_);
lean_dec_ref(v_funDecl_1947_);
v___x_1958_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1946_, v_params_1955_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1946_, v_params_1955_, v_type_1956_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1961_, v_a_1948_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1989_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1989_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1989_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1946_, v_value_1957_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1988_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1988_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1988_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = 1;
v___x_1973_ = l_Lean_Name_toString(v_binderName_1954_, v___x_1972_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 3);
lean_ctor_set(v___x_1965_, 0, v___x_1973_);
v___x_1975_ = v___x_1965_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_a_1959_);
v___x_1977_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_a_1963_);
v___x_1980_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = l_Std_Format_indentD(v_a_1968_);
v___x_1983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1983_);
v___x_1985_ = v___x_1970_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
lean_dec(v_a_1959_);
lean_dec(v_binderName_1954_);
return v___x_1967_;
}
}
}
else
{
lean_dec(v_a_1959_);
lean_dec_ref(v_value_1957_);
lean_dec(v_binderName_1954_);
return v___x_1962_;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1959_);
lean_dec_ref(v_value_1957_);
lean_dec(v_binderName_1954_);
v_a_1990_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1960_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1960_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_dec_ref(v_value_1957_);
lean_dec_ref(v_type_1956_);
lean_dec_ref(v_params_1955_);
lean_dec(v_binderName_1954_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_1998_, lean_object* v_funDecl_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
uint8_t v_pu_boxed_2006_; lean_object* v_res_2007_; 
v_pu_boxed_2006_ = lean_unbox(v_pu_1998_);
v_res_2007_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_2006_, v_funDecl_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_2008_, lean_object* v_c_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
uint8_t v_pu_boxed_2016_; lean_object* v_res_2017_; 
v_pu_boxed_2016_ = lean_unbox(v_pu_2008_);
v_res_2017_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_2016_, v_c_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_a_2010_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_2021_, lean_object* v_b_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
if (lean_obj_tag(v_b_2022_) == 0)
{
lean_object* v_code_2029_; lean_object* v___x_2030_; 
v_code_2029_ = lean_ctor_get(v_b_2022_, 0);
lean_inc_ref(v_code_2029_);
lean_dec_ref_known(v_b_2022_, 1);
v___x_2030_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_2021_, v_code_2029_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2030_;
}
else
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2038_; 
v_isSharedCheck_2038_ = !lean_is_exclusive(v_b_2022_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_b_2022_, 0);
lean_dec(v_unused_2039_);
v___x_2032_ = v_b_2022_;
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_b_2022_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2034_);
v___x_2036_ = v___x_2032_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_2040_, lean_object* v_b_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
uint8_t v_pu_boxed_2048_; lean_object* v_res_2049_; 
v_pu_boxed_2048_ = lean_unbox(v_pu_2040_);
v_res_2049_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_2048_, v_b_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_2050_, lean_object* v_opt_2051_){
_start:
{
lean_object* v_name_2052_; lean_object* v_defValue_2053_; lean_object* v_map_2054_; lean_object* v___x_2055_; 
v_name_2052_ = lean_ctor_get(v_opt_2051_, 0);
v_defValue_2053_ = lean_ctor_get(v_opt_2051_, 1);
v_map_2054_ = lean_ctor_get(v_opts_2050_, 0);
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2054_, v_name_2052_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_inc(v_defValue_2053_);
return v_defValue_2053_;
}
else
{
lean_object* v_val_2056_; 
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___x_2055_, 1);
if (lean_obj_tag(v_val_2056_) == 3)
{
lean_object* v_v_2057_; 
v_v_2057_ = lean_ctor_get(v_val_2056_, 0);
lean_inc(v_v_2057_);
lean_dec_ref_known(v_val_2056_, 1);
return v_v_2057_;
}
else
{
lean_dec(v_val_2056_);
lean_inc(v_defValue_2053_);
return v_defValue_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_2058_, lean_object* v_opt_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_2058_, v_opt_2059_);
lean_dec_ref(v_opt_2059_);
lean_dec_ref(v_opts_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(lean_object* v_o_2064_, lean_object* v_k_2065_, uint8_t v_v_2066_){
_start:
{
lean_object* v_map_2067_; uint8_t v_hasTrace_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2082_; 
v_map_2067_ = lean_ctor_get(v_o_2064_, 0);
v_hasTrace_2068_ = lean_ctor_get_uint8(v_o_2064_, sizeof(void*)*1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_o_2064_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2070_ = v_o_2064_;
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_map_2067_);
lean_dec(v_o_2064_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2072_, 0, v_v_2066_);
lean_inc(v_k_2065_);
v___x_2073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2065_, v___x_2072_, v_map_2067_);
if (v_hasTrace_2068_ == 0)
{
lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1));
v___x_2075_ = l_Lean_Name_isPrefixOf(v___x_2074_, v_k_2065_);
lean_dec(v_k_2065_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2077_ = v___x_2070_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2073_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*1, v___x_2075_);
return v___x_2077_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v_k_2065_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2080_ = v___x_2070_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*1, v_hasTrace_2068_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___boxed(lean_object* v_o_2083_, lean_object* v_k_2084_, lean_object* v_v_2085_){
_start:
{
uint8_t v_v_boxed_2086_; lean_object* v_res_2087_; 
v_v_boxed_2086_ = lean_unbox(v_v_2085_);
v_res_2087_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_o_2083_, v_k_2084_, v_v_boxed_2086_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_2088_, lean_object* v_opt_2089_, uint8_t v_val_2090_){
_start:
{
lean_object* v_name_2091_; lean_object* v___x_2092_; 
v_name_2091_ = lean_ctor_get(v_opt_2089_, 0);
lean_inc(v_name_2091_);
lean_dec_ref(v_opt_2089_);
v___x_2092_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_opts_2088_, v_name_2091_, v_val_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_2093_, lean_object* v_opt_2094_, lean_object* v_val_2095_){
_start:
{
uint8_t v_val_boxed_2096_; lean_object* v_res_2097_; 
v_val_boxed_2096_ = lean_unbox(v_val_2095_);
v_res_2097_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2093_, v_opt_2094_, v_val_boxed_2096_);
return v_res_2097_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
uint16_t v___y_2109_; lean_object* v___y_2110_; lean_object* v_fileName_2111_; lean_object* v_fileMap_2112_; lean_object* v_currNamespace_2113_; lean_object* v_openDecls_2114_; lean_object* v_initHeartbeats_2115_; lean_object* v_maxHeartbeats_2116_; lean_object* v_quotContext_2117_; lean_object* v_currMacroScope_2118_; lean_object* v_cancelTk_x3f_2119_; lean_object* v_inheritedTraceOptions_2120_; lean_object* v_currRecDepth_2121_; lean_object* v_ref_2122_; uint8_t v_suppressElabErrors_2123_; uint8_t v_checkDeprecated_2124_; uint8_t v_isRecordingDeps_2125_; lean_object* v___y_2126_; lean_object* v_toCold_2146_; lean_object* v_currRecDepth_2147_; lean_object* v_ref_2148_; uint8_t v_suppressElabErrors_2149_; uint8_t v_checkDeprecated_2150_; uint8_t v_isRecordingDeps_2151_; lean_object* v_fileName_2152_; lean_object* v_fileMap_2153_; lean_object* v_options_2154_; lean_object* v_currNamespace_2155_; lean_object* v_openDecls_2156_; lean_object* v_initHeartbeats_2157_; lean_object* v_maxHeartbeats_2158_; lean_object* v_quotContext_2159_; lean_object* v_currMacroScope_2160_; lean_object* v_cancelTk_x3f_2161_; lean_object* v_inheritedTraceOptions_2162_; uint16_t v___y_2164_; lean_object* v___y_2165_; uint8_t v___y_2166_; lean_object* v___y_2189_; 
v_toCold_2146_ = lean_ctor_get(v_a_2105_, 0);
v_currRecDepth_2147_ = lean_ctor_get(v_a_2105_, 1);
v_ref_2148_ = lean_ctor_get(v_a_2105_, 2);
v_suppressElabErrors_2149_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*3 + 2);
v_checkDeprecated_2150_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2151_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*3 + 4);
v_fileName_2152_ = lean_ctor_get(v_toCold_2146_, 0);
v_fileMap_2153_ = lean_ctor_get(v_toCold_2146_, 1);
v_options_2154_ = lean_ctor_get(v_toCold_2146_, 2);
v_currNamespace_2155_ = lean_ctor_get(v_toCold_2146_, 4);
v_openDecls_2156_ = lean_ctor_get(v_toCold_2146_, 5);
v_initHeartbeats_2157_ = lean_ctor_get(v_toCold_2146_, 6);
v_maxHeartbeats_2158_ = lean_ctor_get(v_toCold_2146_, 7);
v_quotContext_2159_ = lean_ctor_get(v_toCold_2146_, 8);
v_currMacroScope_2160_ = lean_ctor_get(v_toCold_2146_, 9);
v_cancelTk_x3f_2161_ = lean_ctor_get(v_toCold_2146_, 10);
v_inheritedTraceOptions_2162_ = lean_ctor_get(v_toCold_2146_, 11);
if (v_isRecordingDeps_2151_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = l_Lean_pp_sanitizeNames;
lean_inc_ref(v_options_2154_);
v___x_2201_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_options_2154_, v___x_2200_, v_isRecordingDeps_2151_);
v___y_2189_ = v___x_2201_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2202_; 
lean_inc_ref(v_options_2154_);
v___x_2202_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2154_);
v___y_2189_ = v___x_2202_;
goto v___jp_2188_;
}
v___jp_2108_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = l_Lean_maxRecDepth;
v___x_2128_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v___y_2110_, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2129_, 0, v_fileName_2111_);
lean_ctor_set(v___x_2129_, 1, v_fileMap_2112_);
lean_ctor_set(v___x_2129_, 2, v___y_2110_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
lean_ctor_set(v___x_2129_, 4, v_currNamespace_2113_);
lean_ctor_set(v___x_2129_, 5, v_openDecls_2114_);
lean_ctor_set(v___x_2129_, 6, v_initHeartbeats_2115_);
lean_ctor_set(v___x_2129_, 7, v_maxHeartbeats_2116_);
lean_ctor_set(v___x_2129_, 8, v_quotContext_2117_);
lean_ctor_set(v___x_2129_, 9, v_currMacroScope_2118_);
lean_ctor_set(v___x_2129_, 10, v_cancelTk_x3f_2119_);
lean_ctor_set(v___x_2129_, 11, v_inheritedTraceOptions_2120_);
lean_inc(v_ref_2122_);
lean_inc(v_currRecDepth_2121_);
v___x_2130_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_currRecDepth_2121_);
lean_ctor_set(v___x_2130_, 2, v_ref_2122_);
lean_ctor_set_uint16(v___x_2130_, sizeof(void*)*3, v___y_2109_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*3 + 2, v_suppressElabErrors_2123_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*3 + 3, v_checkDeprecated_2124_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*3 + 4, v_isRecordingDeps_2125_);
v___x_2131_ = lean_st_ref_get(v_a_2104_);
v___x_2132_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2103_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_lctx_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_lctx_2134_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_ref(v_lctx_2134_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_unbox(v_a_2133_);
lean_dec(v_a_2133_);
v___x_2136_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2134_, v___x_2135_);
lean_dec_ref(v_lctx_2134_);
lean_inc(v___y_2126_);
lean_inc(v_a_2104_);
lean_inc_ref(v_a_2103_);
v___x_2137_ = lean_apply_6(v_x_2102_, v___x_2136_, v_a_2103_, v_a_2104_, v___x_2130_, v___y_2126_, lean_box(0));
return v___x_2137_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v___x_2131_);
lean_dec_ref_known(v___x_2130_, 3);
lean_dec_ref(v_x_2102_);
v_a_2138_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2132_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2132_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
v___jp_2163_:
{
lean_object* v___x_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_traceState_2172_; lean_object* v_recordedDeps_2173_; lean_object* v_messages_2174_; lean_object* v_infoState_2175_; lean_object* v_snapshotTasks_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2186_; 
v___x_2167_ = lean_st_ref_take(v_a_2106_);
v_env_2168_ = lean_ctor_get(v___x_2167_, 0);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2167_, 1);
v_ngen_2170_ = lean_ctor_get(v___x_2167_, 2);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2167_, 3);
v_traceState_2172_ = lean_ctor_get(v___x_2167_, 4);
v_recordedDeps_2173_ = lean_ctor_get(v___x_2167_, 6);
v_messages_2174_ = lean_ctor_get(v___x_2167_, 7);
v_infoState_2175_ = lean_ctor_get(v___x_2167_, 8);
v_snapshotTasks_2176_ = lean_ctor_get(v___x_2167_, 9);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v___x_2167_, 5);
lean_dec(v_unused_2187_);
v___x_2178_ = v___x_2167_;
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snapshotTasks_2176_);
lean_inc(v_infoState_2175_);
lean_inc(v_messages_2174_);
lean_inc(v_recordedDeps_2173_);
lean_inc(v_traceState_2172_);
lean_inc(v_auxDeclNGen_2171_);
lean_inc(v_ngen_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_env_2168_);
lean_dec(v___x_2167_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = l_Lean_Kernel_enableDiag(v_env_2168_, v___y_2166_);
v___x_2181_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 5, v___x_2181_);
lean_ctor_set(v___x_2178_, 0, v___x_2180_);
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_ngen_2170_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_auxDeclNGen_2171_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_traceState_2172_);
lean_ctor_set(v_reuseFailAlloc_2185_, 5, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2185_, 6, v_recordedDeps_2173_);
lean_ctor_set(v_reuseFailAlloc_2185_, 7, v_messages_2174_);
lean_ctor_set(v_reuseFailAlloc_2185_, 8, v_infoState_2175_);
lean_ctor_set(v_reuseFailAlloc_2185_, 9, v_snapshotTasks_2176_);
v___x_2183_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_st_ref_put(v_a_2106_, v___x_2183_);
lean_inc_ref(v_inheritedTraceOptions_2162_);
lean_inc(v_cancelTk_x3f_2161_);
lean_inc(v_currMacroScope_2160_);
lean_inc(v_quotContext_2159_);
lean_inc(v_maxHeartbeats_2158_);
lean_inc(v_initHeartbeats_2157_);
lean_inc(v_openDecls_2156_);
lean_inc(v_currNamespace_2155_);
lean_inc_ref(v_fileMap_2153_);
lean_inc_ref(v_fileName_2152_);
v___y_2109_ = v___y_2164_;
v___y_2110_ = v___y_2165_;
v_fileName_2111_ = v_fileName_2152_;
v_fileMap_2112_ = v_fileMap_2153_;
v_currNamespace_2113_ = v_currNamespace_2155_;
v_openDecls_2114_ = v_openDecls_2156_;
v_initHeartbeats_2115_ = v_initHeartbeats_2157_;
v_maxHeartbeats_2116_ = v_maxHeartbeats_2158_;
v_quotContext_2117_ = v_quotContext_2159_;
v_currMacroScope_2118_ = v_currMacroScope_2160_;
v_cancelTk_x3f_2119_ = v_cancelTk_x3f_2161_;
v_inheritedTraceOptions_2120_ = v_inheritedTraceOptions_2162_;
v_currRecDepth_2121_ = v_currRecDepth_2147_;
v_ref_2122_ = v_ref_2148_;
v_suppressElabErrors_2123_ = v_suppressElabErrors_2149_;
v_checkDeprecated_2124_ = v_checkDeprecated_2150_;
v_isRecordingDeps_2125_ = v_isRecordingDeps_2151_;
v___y_2126_ = v_a_2106_;
goto v___jp_2108_;
}
}
}
v___jp_2188_:
{
uint16_t v___x_2190_; lean_object* v___x_2191_; lean_object* v_env_2192_; uint8_t v___x_2193_; uint16_t v___x_2194_; uint16_t v___x_2195_; uint16_t v___x_2196_; uint8_t v___x_2197_; 
v___x_2190_ = l_Lean_OptionFlags_ofOptions(v___y_2189_);
v___x_2191_ = lean_st_ref_get(v_a_2106_);
v_env_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc_ref(v_env_2192_);
lean_dec(v___x_2191_);
v___x_2193_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2192_);
lean_dec_ref(v_env_2192_);
v___x_2194_ = 512;
v___x_2195_ = lean_uint16_land(v___x_2190_, v___x_2194_);
v___x_2196_ = 0;
v___x_2197_ = lean_uint16_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
if (v___x_2193_ == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = 1;
v___y_2164_ = v___x_2190_;
v___y_2165_ = v___y_2189_;
v___y_2166_ = v___x_2198_;
goto v___jp_2163_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2162_);
lean_inc(v_cancelTk_x3f_2161_);
lean_inc(v_currMacroScope_2160_);
lean_inc(v_quotContext_2159_);
lean_inc(v_maxHeartbeats_2158_);
lean_inc(v_initHeartbeats_2157_);
lean_inc(v_openDecls_2156_);
lean_inc(v_currNamespace_2155_);
lean_inc_ref(v_fileMap_2153_);
lean_inc_ref(v_fileName_2152_);
v___y_2109_ = v___x_2190_;
v___y_2110_ = v___y_2189_;
v_fileName_2111_ = v_fileName_2152_;
v_fileMap_2112_ = v_fileMap_2153_;
v_currNamespace_2113_ = v_currNamespace_2155_;
v_openDecls_2114_ = v_openDecls_2156_;
v_initHeartbeats_2115_ = v_initHeartbeats_2157_;
v_maxHeartbeats_2116_ = v_maxHeartbeats_2158_;
v_quotContext_2117_ = v_quotContext_2159_;
v_currMacroScope_2118_ = v_currMacroScope_2160_;
v_cancelTk_x3f_2119_ = v_cancelTk_x3f_2161_;
v_inheritedTraceOptions_2120_ = v_inheritedTraceOptions_2162_;
v_currRecDepth_2121_ = v_currRecDepth_2147_;
v_ref_2122_ = v_ref_2148_;
v_suppressElabErrors_2123_ = v_suppressElabErrors_2149_;
v_checkDeprecated_2124_ = v_checkDeprecated_2150_;
v_isRecordingDeps_2125_ = v_isRecordingDeps_2151_;
v___y_2126_ = v_a_2106_;
goto v___jp_2108_;
}
}
else
{
if (v___x_2193_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2162_);
lean_inc(v_cancelTk_x3f_2161_);
lean_inc(v_currMacroScope_2160_);
lean_inc(v_quotContext_2159_);
lean_inc(v_maxHeartbeats_2158_);
lean_inc(v_initHeartbeats_2157_);
lean_inc(v_openDecls_2156_);
lean_inc(v_currNamespace_2155_);
lean_inc_ref(v_fileMap_2153_);
lean_inc_ref(v_fileName_2152_);
v___y_2109_ = v___x_2190_;
v___y_2110_ = v___y_2189_;
v_fileName_2111_ = v_fileName_2152_;
v_fileMap_2112_ = v_fileMap_2153_;
v_currNamespace_2113_ = v_currNamespace_2155_;
v_openDecls_2114_ = v_openDecls_2156_;
v_initHeartbeats_2115_ = v_initHeartbeats_2157_;
v_maxHeartbeats_2116_ = v_maxHeartbeats_2158_;
v_quotContext_2117_ = v_quotContext_2159_;
v_currMacroScope_2118_ = v_currMacroScope_2160_;
v_cancelTk_x3f_2119_ = v_cancelTk_x3f_2161_;
v_inheritedTraceOptions_2120_ = v_inheritedTraceOptions_2162_;
v_currRecDepth_2121_ = v_currRecDepth_2147_;
v_ref_2122_ = v_ref_2148_;
v_suppressElabErrors_2123_ = v_suppressElabErrors_2149_;
v_checkDeprecated_2124_ = v_checkDeprecated_2150_;
v_isRecordingDeps_2125_ = v_isRecordingDeps_2151_;
v___y_2126_ = v_a_2106_;
goto v___jp_2108_;
}
else
{
uint8_t v___x_2199_; 
v___x_2199_ = 0;
v___y_2164_ = v___x_2190_;
v___y_2165_ = v___y_2189_;
v___y_2166_ = v___x_2199_;
goto v___jp_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2210_, lean_object* v_x_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2218_, v_x_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2226_, lean_object* v_code_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_box(v_pu_2226_);
v___x_2234_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2234_, 0, v___x_2233_);
lean_closure_set(v___x_2234_, 1, v_code_2227_);
v___x_2235_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2234_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2236_, lean_object* v_code_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
uint8_t v_pu_boxed_2243_; lean_object* v_res_2244_; 
v_pu_boxed_2243_ = lean_unbox(v_pu_2236_);
v_res_2244_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2243_, v_code_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2245_, lean_object* v_e_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_box(v_pu_2245_);
v___x_2253_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2253_, 0, v___x_2252_);
lean_closure_set(v___x_2253_, 1, v_e_2246_);
v___x_2254_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2253_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2255_, lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
uint8_t v_pu_boxed_2262_; lean_object* v_res_2263_; 
v_pu_boxed_2262_ = lean_unbox(v_pu_2255_);
v_res_2263_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2262_, v_e_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2267_, lean_object* v_params_2268_, lean_object* v_type_2269_, lean_object* v_value_2270_, lean_object* v_name_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2267_, v_params_2268_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2267_, v_params_2268_, v_type_2269_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2281_, v___y_2272_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2311_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2311_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2311_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2267_, v_value_2270_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2310_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2310_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2310_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2292_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2293_ = 1;
v___x_2294_ = l_Lean_Name_toString(v_name_2271_, v___x_2293_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 3);
lean_ctor_set(v___x_2285_, 0, v___x_2294_);
v___x_2296_ = v___x_2285_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2292_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v_a_2279_);
v___x_2299_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v_a_2283_);
v___x_2302_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Std_Format_indentD(v_a_2288_);
v___x_2305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2305_);
v___x_2307_ = v___x_2290_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_del_object(v___x_2285_);
lean_dec(v_a_2283_);
lean_dec(v_a_2279_);
lean_dec(v_name_2271_);
return v___x_2287_;
}
}
}
else
{
lean_dec(v_a_2279_);
lean_dec(v_name_2271_);
lean_dec_ref(v_value_2270_);
return v___x_2282_;
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2279_);
lean_dec(v_name_2271_);
lean_dec_ref(v_value_2270_);
v_a_2312_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2280_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2280_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_dec(v_name_2271_);
lean_dec_ref(v_value_2270_);
lean_dec_ref(v_type_2269_);
lean_dec_ref(v_params_2268_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2320_, lean_object* v_params_2321_, lean_object* v_type_2322_, lean_object* v_value_2323_, lean_object* v_name_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v_pu_boxed_2331_; lean_object* v_res_2332_; 
v_pu_boxed_2331_ = lean_unbox(v_pu_2320_);
v_res_2332_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2331_, v_params_2321_, v_type_2322_, v_value_2323_, v_name_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2333_, lean_object* v_decl_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_toSignature_2340_; lean_object* v_value_2341_; lean_object* v_name_2342_; lean_object* v_type_2343_; lean_object* v_params_2344_; lean_object* v___x_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; 
v_toSignature_2340_ = lean_ctor_get(v_decl_2334_, 0);
lean_inc_ref(v_toSignature_2340_);
v_value_2341_ = lean_ctor_get(v_decl_2334_, 1);
lean_inc_ref(v_value_2341_);
lean_dec_ref(v_decl_2334_);
v_name_2342_ = lean_ctor_get(v_toSignature_2340_, 0);
lean_inc(v_name_2342_);
v_type_2343_ = lean_ctor_get(v_toSignature_2340_, 2);
lean_inc_ref(v_type_2343_);
v_params_2344_ = lean_ctor_get(v_toSignature_2340_, 3);
lean_inc_ref(v_params_2344_);
lean_dec_ref(v_toSignature_2340_);
v___x_2345_ = lean_box(v_pu_2333_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2346_, 0, v___x_2345_);
lean_closure_set(v___f_2346_, 1, v_params_2344_);
lean_closure_set(v___f_2346_, 2, v_type_2343_);
lean_closure_set(v___f_2346_, 3, v_value_2341_);
lean_closure_set(v___f_2346_, 4, v_name_2342_);
v___x_2347_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2346_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2348_, lean_object* v_decl_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v_pu_boxed_2355_; lean_object* v_res_2356_; 
v_pu_boxed_2355_ = lean_unbox(v_pu_2348_);
v_res_2356_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2355_, v_decl_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2357_, lean_object* v_decl_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2357_, v_decl_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2375_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2375_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2375_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2370_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v_a_2366_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2371_);
v___x_2373_ = v___x_2368_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
else
{
return v___x_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2376_, lean_object* v_decl_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
uint8_t v_pu_boxed_2384_; lean_object* v_res_2385_; 
v_pu_boxed_2384_ = lean_unbox(v_pu_2376_);
v_res_2385_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2384_, v_decl_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2386_, lean_object* v_decl_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_box(v_pu_2386_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2394_, 0, v___x_2393_);
lean_closure_set(v___f_2394_, 1, v_decl_2387_);
v___x_2395_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2394_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2396_, lean_object* v_decl_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v_pu_boxed_2403_; lean_object* v_res_2404_; 
v_pu_boxed_2403_ = lean_unbox(v_pu_2396_);
v_res_2404_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2403_, v_decl_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2405_, lean_object* v_val_2406_, lean_object* v_a_x3f_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_st_ref_swap(v_a_2405_, v_val_2406_);
lean_dec(v___x_2410_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2412_, lean_object* v_val_2413_, lean_object* v_a_x3f_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2412_, v_val_2413_, v_a_x3f_2414_);
lean_dec(v_a_x3f_2414_);
lean_dec(v_a_2412_);
return v_res_2416_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_unsigned_to_nat(16u);
v___x_2419_ = lean_mk_array(v___x_2418_, v___x_2417_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2424_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_ctor_set(v___x_2424_, 2, v___x_2423_);
lean_ctor_set(v___x_2424_, 3, v___x_2423_);
lean_ctor_set(v___x_2424_, 4, v___x_2423_);
lean_ctor_set(v___x_2424_, 5, v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2428_, lean_object* v_x_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_r_2435_; 
v___x_2433_ = lean_st_ref_get(v_a_2431_);
v___x_2434_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2435_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2429_, v___x_2434_, v_phase_2428_, v_a_2430_, v_a_2431_);
if (lean_obj_tag(v_r_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2452_; 
v_a_2436_ = lean_ctor_get(v_r_2435_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_r_2435_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2438_ = v_r_2435_;
v_isShared_2439_ = v_isSharedCheck_2452_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v_r_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2452_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
lean_inc(v_a_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
v___x_2442_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2431_, v___x_2433_, v___x_2441_);
lean_dec_ref(v___x_2441_);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; 
v_unused_2450_ = lean_ctor_get(v___x_2442_, 0);
lean_dec(v_unused_2450_);
v___x_2444_ = v___x_2442_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_dec(v___x_2442_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v_a_2436_);
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2436_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2453_ = lean_ctor_get(v_r_2435_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v_r_2435_, 1);
v___x_2454_ = lean_box(0);
v___x_2455_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2431_, v___x_2433_, v___x_2454_);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2463_);
v___x_2457_ = v___x_2455_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 1);
lean_ctor_set(v___x_2457_, 0, v_a_2453_);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2453_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2464_, lean_object* v_x_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
uint8_t v_phase_boxed_2469_; lean_object* v_res_2470_; 
v_phase_boxed_2469_ = lean_unbox(v_phase_2464_);
v_res_2470_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2469_, v_x_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2471_, uint8_t v_phase_2472_, lean_object* v_x_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2472_, v_x_2473_, v_a_2474_, v_a_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_phase_2479_, lean_object* v_x_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
uint8_t v_phase_boxed_2484_; lean_object* v_res_2485_; 
v_phase_boxed_2484_ = lean_unbox(v_phase_2479_);
v_res_2485_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2478_, v_phase_boxed_2484_, v_x_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2486_, lean_object* v_decl_2487_, lean_object* v___x_2488_, uint8_t v___x_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2486_, v_decl_2487_, v___x_2488_, v___x_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2486_, v_a_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2497_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2495_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2495_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2506_, lean_object* v_decl_2507_, lean_object* v___x_2508_, lean_object* v___x_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v_pu_boxed_2515_; uint8_t v___x_100__boxed_2516_; lean_object* v_res_2517_; 
v_pu_boxed_2515_ = lean_unbox(v_pu_2506_);
v___x_100__boxed_2516_ = lean_unbox(v___x_2509_);
v_res_2517_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2515_, v_decl_2507_, v___x_2508_, v___x_100__boxed_2516_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2518_, lean_object* v_decl_2519_, uint8_t v_phase_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; 
v___x_2524_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2525_ = 0;
v___x_2526_ = lean_box(v_pu_2518_);
v___x_2527_ = lean_box(v___x_2525_);
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2528_, 0, v___x_2526_);
lean_closure_set(v___f_2528_, 1, v_decl_2519_);
lean_closure_set(v___f_2528_, 2, v___x_2524_);
lean_closure_set(v___f_2528_, 3, v___x_2527_);
v___x_2529_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2520_, v___f_2528_, v_a_2521_, v_a_2522_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2530_, lean_object* v_decl_2531_, lean_object* v_phase_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
uint8_t v_pu_boxed_2536_; uint8_t v_phase_boxed_2537_; lean_object* v_res_2538_; 
v_pu_boxed_2536_ = lean_unbox(v_pu_2530_);
v_phase_boxed_2537_ = lean_unbox(v_phase_2532_);
v_res_2538_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2536_, v_decl_2531_, v_phase_boxed_2537_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2539_, lean_object* v_code_2540_, lean_object* v___x_2541_, uint8_t v___x_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2539_, v_code_2540_, v___x_2541_, v___x_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2539_, v_a_2549_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
return v___x_2550_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2548_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2559_, lean_object* v_code_2560_, lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v_pu_boxed_2568_; uint8_t v___x_100__boxed_2569_; lean_object* v_res_2570_; 
v_pu_boxed_2568_ = lean_unbox(v_pu_2559_);
v___x_100__boxed_2569_ = lean_unbox(v___x_2562_);
v_res_2570_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2568_, v_code_2560_, v___x_2561_, v___x_100__boxed_2569_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2571_, lean_object* v_code_2572_, uint8_t v_phase_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___x_2577_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2578_ = 0;
v___x_2579_ = lean_box(v_pu_2571_);
v___x_2580_ = lean_box(v___x_2578_);
v___f_2581_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2581_, 0, v___x_2579_);
lean_closure_set(v___f_2581_, 1, v_code_2572_);
lean_closure_set(v___f_2581_, 2, v___x_2577_);
lean_closure_set(v___f_2581_, 3, v___x_2580_);
v___x_2582_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2573_, v___f_2581_, v_a_2574_, v_a_2575_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2583_, lean_object* v_code_2584_, lean_object* v_phase_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_pu_boxed_2589_; uint8_t v_phase_boxed_2590_; lean_object* v_res_2591_; 
v_pu_boxed_2589_ = lean_unbox(v_pu_2583_);
v_phase_boxed_2590_ = lean_unbox(v_phase_2585_);
v_res_2591_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2589_, v_code_2584_, v_phase_boxed_2590_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2591_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
}
#ifdef __cplusplus
}
#endif

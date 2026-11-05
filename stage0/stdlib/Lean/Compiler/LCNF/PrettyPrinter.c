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
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13;
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
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v___x_317_);
lean_ctor_set(v___x_318_, 4, v___x_316_);
lean_ctor_set(v___x_318_, 5, v___x_316_);
lean_ctor_set(v___x_318_, 6, v___x_316_);
lean_ctor_set(v___x_318_, 7, v___x_316_);
lean_ctor_set(v___x_318_, 8, v___x_316_);
lean_ctor_set(v___x_318_, 9, v___x_316_);
lean_ctor_set(v___x_318_, 10, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg();
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_325_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
v___x_326_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
v___x_327_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_328_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
v___x_329_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_326_);
lean_ctor_set(v___x_329_, 3, v___x_327_);
lean_ctor_set(v___x_329_, 4, v___x_327_);
lean_ctor_set(v___x_329_, 5, v___x_327_);
lean_ctor_set(v___x_329_, 6, v___x_327_);
lean_ctor_set(v___x_329_, 7, v___x_325_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(32u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11(void){
_start:
{
size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_333_ = ((size_t)5ULL);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10);
v___x_338_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_334_);
lean_ctor_set(v___x_338_, 3, v___x_334_);
lean_ctor_set_usize(v___x_338_, 4, v___x_333_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
lean_ctor_set(v___x_340_, 4, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__12);
v___x_342_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11);
v___x_343_ = lean_box(1);
v___x_344_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
v___x_345_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
lean_ctor_set(v___x_346_, 3, v___x_342_);
lean_ctor_set(v___x_346_, 4, v___x_341_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_352_ = lean_box(1);
v___x_353_ = 0;
v___x_354_ = 1;
v___x_355_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3));
v___x_358_ = lean_box(0);
lean_inc_ref(v_a_348_);
v___x_359_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_359_, 0, v___x_355_);
lean_ctor_set(v___x_359_, 1, v___x_352_);
lean_ctor_set(v___x_359_, 2, v_a_348_);
lean_ctor_set(v___x_359_, 3, v___x_357_);
lean_ctor_set(v___x_359_, 4, v___x_358_);
lean_ctor_set(v___x_359_, 5, v___x_356_);
lean_ctor_set(v___x_359_, 6, v___x_358_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7, v___x_353_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 1, v___x_353_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 2, v___x_353_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 3, v___x_354_);
v___x_360_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__13);
v___x_361_ = lean_st_mk_ref(v___x_360_);
v___x_362_ = l_Lean_Meta_ppExpr(v_e_347_, v___x_359_, v___x_361_, v_a_349_, v_a_350_);
lean_dec_ref_known(v___x_359_, 7);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_371_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_st_ref_get(v___x_361_);
lean_dec(v___x_361_);
lean_dec(v___x_367_);
if (v_isShared_366_ == 0)
{
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_363_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_dec(v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_378_, v_a_379_, v_a_382_, v_a_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* v_e_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0(lean_object* v_00_u03b2_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg___boxed(lean_object* v___dummy_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0___redArg();
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0(lean_object* v_00_u03b2_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
return v___x_401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* v_opts_402_, lean_object* v_opt_403_){
_start:
{
lean_object* v_name_404_; lean_object* v_defValue_405_; lean_object* v_map_406_; lean_object* v___x_407_; 
v_name_404_ = lean_ctor_get(v_opt_403_, 0);
v_defValue_405_ = lean_ctor_get(v_opt_403_, 1);
v_map_406_ = lean_ctor_get(v_opts_402_, 0);
v___x_407_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_406_, v_name_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
uint8_t v___x_408_; 
v___x_408_ = lean_unbox(v_defValue_405_);
return v___x_408_;
}
else
{
lean_object* v_val_409_; 
v_val_409_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_407_, 1);
if (lean_obj_tag(v_val_409_) == 1)
{
uint8_t v_v_410_; 
v_v_410_ = lean_ctor_get_uint8(v_val_409_, 0);
lean_dec_ref_known(v_val_409_, 0);
return v_v_410_;
}
else
{
uint8_t v___x_411_; 
lean_dec(v_val_409_);
v___x_411_ = lean_unbox(v_defValue_405_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* v_opts_412_, lean_object* v_opt_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_412_, v_opt_413_);
lean_dec_ref(v_opt_413_);
lean_dec_ref(v_opts_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* v_a_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_nat_to_int(v_a_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
v___x_427_ = lean_string_length(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
v___x_429_ = lean_nat_to_int(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* v_e_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
switch(lean_obj_tag(v_e_434_))
{
case 0:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
case 1:
{
lean_object* v_fvarId_443_; lean_object* v___x_444_; 
v_fvarId_443_ = lean_ctor_get(v_e_434_, 0);
lean_inc(v_fvarId_443_);
lean_dec_ref_known(v_e_434_, 1);
v___x_444_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_443_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
return v___x_444_;
}
default: 
{
lean_object* v_expr_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_481_; 
v_expr_445_ = lean_ctor_get(v_e_434_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_e_434_);
if (v_isSharedCheck_481_ == 0)
{
v___x_447_ = v_e_434_;
v_isShared_448_ = v_isSharedCheck_481_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_expr_445_);
lean_dec(v_e_434_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_481_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_449_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_438_);
v___x_450_ = l_Lean_pp_explicit;
v___x_451_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_449_, v___x_450_);
lean_dec_ref(v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref(v_expr_445_);
v___x_452_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 0);
lean_ctor_set(v___x_447_, 0, v___x_452_);
v___x_454_ = v___x_447_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
uint8_t v___x_456_; 
lean_del_object(v___x_447_);
v___x_456_ = l_Lean_Expr_isConst(v_expr_445_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Expr_isProp(v_expr_445_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = l_Lean_Expr_isType0(v_expr_445_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_Expr_isFVar(v_expr_445_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_445_, v_a_435_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_476_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_476_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_476_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_476_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_466_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_461_);
v___x_468_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_465_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_472_);
v___x_474_ = v___x_463_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
return v___x_460_;
}
}
else
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_445_, v_a_435_, v_a_438_, v_a_439_);
return v___x_477_;
}
}
else
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_445_, v_a_435_, v_a_438_, v_a_439_);
return v___x_478_;
}
}
else
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_445_, v_a_435_, v_a_438_, v_a_439_);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_445_, v_a_435_, v_a_438_, v_a_439_);
return v___x_480_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t v_pu_490_, lean_object* v_e_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* v_pu_499_, lean_object* v_e_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v_pu_boxed_507_; lean_object* v_res_508_; 
v_pu_boxed_507_ = lean_unbox(v_pu_499_);
v_res_508_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_boxed_507_, v_e_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t v_pu_509_, lean_object* v_args_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_518_ = lean_box(v_pu_509_);
v___x_519_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(v___x_519_, 0, v___x_518_);
v___x_520_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_517_, v_args_510_, v___x_519_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* v_pu_521_, lean_object* v_args_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
uint8_t v_pu_boxed_529_; lean_object* v_res_530_; 
v_pu_boxed_529_ = lean_unbox(v_pu_521_);
v_res_530_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_boxed_529_, v_args_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec_ref(v_args_522_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* v_lit_531_){
_start:
{
uint64_t v_v_534_; 
switch(lean_obj_tag(v_lit_531_))
{
case 0:
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
v_val_539_ = lean_ctor_get(v_lit_531_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_lit_531_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v_lit_531_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v_lit_531_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = l_Nat_reprFast(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 3);
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
case 1:
{
lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
v_val_549_ = lean_ctor_get(v_lit_531_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_lit_531_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v_lit_531_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v_lit_531_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_String_quote(v_val_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 3);
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
case 2:
{
uint8_t v_val_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_val_559_ = lean_ctor_get_uint8(v_lit_531_, 0);
lean_dec_ref_known(v_lit_531_, 0);
v___x_560_ = lean_uint8_to_nat(v_val_559_);
v___x_561_ = l_Nat_reprFast(v___x_560_);
v___x_562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
case 3:
{
uint16_t v_val_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_val_564_ = lean_ctor_get_uint16(v_lit_531_, 0);
lean_dec_ref_known(v_lit_531_, 0);
v___x_565_ = lean_uint16_to_nat(v_val_564_);
v___x_566_ = l_Nat_reprFast(v___x_565_);
v___x_567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
case 4:
{
uint32_t v_val_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_val_569_ = lean_ctor_get_uint32(v_lit_531_, 0);
lean_dec_ref_known(v_lit_531_, 0);
v___x_570_ = lean_uint32_to_nat(v_val_569_);
v___x_571_ = l_Nat_reprFast(v___x_570_);
v___x_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
default: 
{
uint64_t v_val_574_; 
v_val_574_ = lean_ctor_get_uint64(v_lit_531_, 0);
lean_dec_ref(v_lit_531_);
v_v_534_ = v_val_574_;
goto v___jp_533_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = lean_uint64_to_nat(v_v_534_);
v___x_536_ = l_Nat_reprFast(v___x_535_);
v___x_537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* v_lit_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* v_lit_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_578_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* v_lit_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* v_x_606_){
_start:
{
lean_object* v_name_607_; lean_object* v_cidx_608_; lean_object* v_usize_609_; lean_object* v_ssize_610_; lean_object* v_r_612_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_r_626_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_name_607_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_name_607_);
v_cidx_608_ = lean_ctor_get(v_x_606_, 1);
lean_inc(v_cidx_608_);
v_usize_609_ = lean_ctor_get(v_x_606_, 3);
lean_inc(v_usize_609_);
v_ssize_610_ = lean_ctor_get(v_x_606_, 4);
lean_inc(v_ssize_610_);
lean_dec_ref(v_x_606_);
v___x_623_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
v___x_624_ = l_Nat_reprFast(v_cidx_608_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v_r_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_626_, 0, v___x_623_);
lean_ctor_set(v_r_626_, 1, v___x_625_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_nat_dec_lt(v___x_637_, v_usize_609_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_lt(v___x_637_, v_ssize_610_);
if (v___x_639_ == 0)
{
lean_dec(v_ssize_610_);
lean_dec(v_usize_609_);
v_r_612_ = v_r_626_;
goto v___jp_611_;
}
else
{
goto v___jp_627_;
}
}
else
{
goto v___jp_627_;
}
v___jp_611_:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_box(0);
v___x_614_ = lean_name_eq(v_name_607_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_r_622_; 
v___x_615_ = 1;
v___x_616_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v_r_612_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_Name_toString(v_name_607_, v___x_615_);
v___x_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v_r_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_622_, 0, v___x_620_);
lean_ctor_set(v_r_622_, 1, v___x_621_);
return v_r_622_;
}
else
{
lean_dec(v_name_607_);
return v_r_612_;
}
}
v___jp_627_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_r_636_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v_r_626_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Nat_reprFast(v_usize_609_);
v___x_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_628_);
v___x_634_ = l_Nat_reprFast(v_ssize_610_);
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v_r_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_636_, 0, v___x_633_);
lean_ctor_set(v_r_636_, 1, v___x_635_);
v_r_612_ = v_r_636_;
goto v___jp_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_689_, lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
switch(lean_obj_tag(v_e_690_))
{
case 0:
{
lean_object* v_value_697_; lean_object* v___x_698_; 
v_value_697_ = lean_ctor_get(v_e_690_, 0);
lean_inc_ref(v_value_697_);
lean_dec_ref_known(v_e_690_, 1);
v___x_698_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_697_);
return v___x_698_;
}
case 1:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
case 2:
{
lean_object* v_idx_701_; lean_object* v_struct_702_; lean_object* v___x_703_; 
v_idx_701_ = lean_ctor_get(v_e_690_, 1);
lean_inc(v_idx_701_);
v_struct_702_ = lean_ctor_get(v_e_690_, 2);
lean_inc(v_struct_702_);
lean_dec_ref_known(v_e_690_, 3);
v___x_703_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_702_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_716_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_716_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_716_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_716_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_708_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v_a_704_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Nat_reprFast(v_idx_701_);
v___x_711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
v___x_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_709_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_712_);
v___x_714_ = v___x_706_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_dec(v_idx_701_);
return v___x_703_;
}
}
case 3:
{
lean_object* v_declName_717_; lean_object* v_us_718_; lean_object* v_args_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_declName_717_ = lean_ctor_get(v_e_690_, 0);
lean_inc(v_declName_717_);
v_us_718_ = lean_ctor_get(v_e_690_, 1);
lean_inc(v_us_718_);
v_args_719_ = lean_ctor_get(v_e_690_, 2);
lean_inc_ref(v_args_719_);
lean_dec_ref_known(v_e_690_, 3);
v___x_720_ = l_Lean_Expr_const___override(v_declName_717_, v_us_718_);
v___x_721_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_720_, v_a_691_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_719_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_719_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_722_);
lean_ctor_set(v___x_728_, 1, v_a_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_dec(v_a_722_);
return v___x_723_;
}
}
else
{
lean_dec_ref(v_args_719_);
return v___x_721_;
}
}
case 4:
{
lean_object* v_fvarId_733_; lean_object* v_args_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_752_; 
v_fvarId_733_ = lean_ctor_get(v_e_690_, 0);
v_args_734_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_752_ == 0)
{
v___x_736_ = v_e_690_;
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_args_734_);
lean_inc(v_fvarId_733_);
lean_dec(v_e_690_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_733_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_734_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_734_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_751_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 5);
lean_ctor_set(v___x_736_, 1, v_a_741_);
lean_ctor_set(v___x_736_, 0, v_a_739_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_739_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_741_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
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
lean_dec(v_a_739_);
lean_del_object(v___x_736_);
return v___x_740_;
}
}
else
{
lean_del_object(v___x_736_);
lean_dec_ref(v_args_734_);
return v___x_738_;
}
}
}
case 5:
{
lean_object* v_i_753_; lean_object* v_args_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_771_; 
v_i_753_ = lean_ctor_get(v_e_690_, 0);
v_args_754_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_771_ == 0)
{
v___x_756_ = v_e_690_;
v_isShared_757_ = v_isSharedCheck_771_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_args_754_);
lean_inc(v_i_753_);
lean_dec(v_e_690_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_771_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_754_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_770_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_a_759_);
lean_ctor_set(v___x_756_, 0, v___x_763_);
v___x_765_ = v___x_756_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_759_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_765_);
v___x_767_ = v___x_761_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_del_object(v___x_756_);
lean_dec_ref(v_i_753_);
return v___x_758_;
}
}
}
case 6:
{
lean_object* v_i_772_; lean_object* v_var_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_795_; 
v_i_772_ = lean_ctor_get(v_e_690_, 0);
v_var_773_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_795_ == 0)
{
v___x_775_ = v_e_690_;
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_var_773_);
lean_inc(v_i_772_);
lean_dec(v_e_690_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_773_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_794_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_794_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_794_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_783_ = l_Nat_reprFast(v_i_772_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 5);
lean_ctor_set(v___x_775_, 1, v___x_784_);
lean_ctor_set(v___x_775_, 0, v___x_782_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_793_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_789_);
v___x_791_ = v___x_780_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_del_object(v___x_775_);
lean_dec(v_i_772_);
return v___x_777_;
}
}
}
case 7:
{
lean_object* v_i_796_; lean_object* v_var_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_819_; 
v_i_796_ = lean_ctor_get(v_e_690_, 0);
v_var_797_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_819_ == 0)
{
v___x_799_ = v_e_690_;
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_var_797_);
lean_inc(v_i_796_);
lean_dec(v_e_690_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_797_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_818_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_806_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
v___x_807_ = l_Nat_reprFast(v_i_796_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 5);
lean_ctor_set(v___x_799_, 1, v___x_808_);
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_810_ = v___x_799_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_817_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_811_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_813_);
v___x_815_ = v___x_804_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_del_object(v___x_799_);
lean_dec(v_i_796_);
return v___x_801_;
}
}
}
case 8:
{
lean_object* v_n_820_; lean_object* v_offset_821_; lean_object* v_var_822_; lean_object* v___x_823_; 
v_n_820_ = lean_ctor_get(v_e_690_, 0);
lean_inc(v_n_820_);
v_offset_821_ = lean_ctor_get(v_e_690_, 1);
lean_inc(v_offset_821_);
v_var_822_ = lean_ctor_get(v_e_690_, 2);
lean_inc(v_var_822_);
lean_dec_ref_known(v_e_690_, 3);
v___x_823_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_822_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_843_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_843_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_828_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_829_ = l_Nat_reprFast(v_n_820_);
v___x_830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Nat_reprFast(v_offset_821_);
v___x_835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_833_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_839_);
v___x_841_ = v___x_826_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_dec(v_offset_821_);
lean_dec(v_n_820_);
return v___x_823_;
}
}
case 9:
{
lean_object* v_fn_844_; lean_object* v_args_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_864_; 
v_fn_844_ = lean_ctor_get(v_e_690_, 0);
v_args_845_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_864_ == 0)
{
v___x_847_ = v_e_690_;
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_args_845_);
lean_inc(v_fn_844_);
lean_dec(v_e_690_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_845_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_845_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_863_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_863_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_854_ = 1;
v___x_855_ = l_Lean_Name_toString(v_fn_844_, v___x_854_);
v___x_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 5);
lean_ctor_set(v___x_847_, 1, v_a_850_);
lean_ctor_set(v___x_847_, 0, v___x_856_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_a_850_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_858_);
v___x_860_ = v___x_852_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_del_object(v___x_847_);
lean_dec(v_fn_844_);
return v___x_849_;
}
}
}
case 10:
{
lean_object* v_fn_865_; lean_object* v_args_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_887_; 
v_fn_865_ = lean_ctor_get(v_e_690_, 0);
v_args_866_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_887_ == 0)
{
v___x_868_ = v_e_690_;
v_isShared_869_ = v_isSharedCheck_887_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_args_866_);
lean_inc(v_fn_865_);
lean_dec(v_e_690_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_887_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_866_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_866_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_886_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_876_ = 1;
v___x_877_ = l_Lean_Name_toString(v_fn_865_, v___x_876_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 5);
lean_ctor_set(v___x_868_, 1, v___x_878_);
lean_ctor_set(v___x_868_, 0, v___x_875_);
v___x_880_ = v___x_868_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_885_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_881_);
v___x_883_ = v___x_873_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
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
else
{
lean_del_object(v___x_868_);
lean_dec(v_fn_865_);
return v___x_870_;
}
}
}
case 11:
{
lean_object* v_n_888_; lean_object* v_var_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_911_; 
v_n_888_ = lean_ctor_get(v_e_690_, 0);
v_var_889_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_911_ == 0)
{
v___x_891_ = v_e_690_;
v_isShared_892_ = v_isSharedCheck_911_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_var_889_);
lean_inc(v_n_888_);
lean_dec(v_e_690_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_911_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_889_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_910_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_910_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_898_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_899_ = l_Nat_reprFast(v_n_888_);
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 5);
lean_ctor_set(v___x_891_, 1, v___x_900_);
lean_ctor_set(v___x_891_, 0, v___x_898_);
v___x_902_ = v___x_891_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_909_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_903_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_a_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_905_);
v___x_907_ = v___x_896_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_del_object(v___x_891_);
lean_dec(v_n_888_);
return v___x_893_;
}
}
}
case 12:
{
lean_object* v_var_912_; lean_object* v_i_913_; uint8_t v_updateHeader_914_; lean_object* v_args_915_; lean_object* v___x_916_; 
v_var_912_ = lean_ctor_get(v_e_690_, 0);
lean_inc(v_var_912_);
v_i_913_ = lean_ctor_get(v_e_690_, 1);
lean_inc_ref(v_i_913_);
v_updateHeader_914_ = lean_ctor_get_uint8(v_e_690_, sizeof(void*)*3);
v_args_915_ = lean_ctor_get(v_e_690_, 2);
lean_inc_ref(v_args_915_);
lean_dec_ref_known(v_e_690_, 3);
v___x_916_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_912_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_689_, v_args_915_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_args_915_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_940_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_940_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_940_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___y_925_; 
v___x_923_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_914_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_925_ = v___x_938_;
goto v___jp_924_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_925_ = v___x_939_;
goto v___jp_924_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v___y_925_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_923_);
lean_ctor_set(v___x_926_, 1, v___y_925_);
v___x_927_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_a_917_);
v___x_929_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_913_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_919_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_926_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_934_);
v___x_936_ = v___x_921_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_dec(v_a_917_);
lean_dec_ref(v_i_913_);
return v___x_918_;
}
}
else
{
lean_dec_ref(v_args_915_);
lean_dec_ref(v_i_913_);
return v___x_916_;
}
}
case 13:
{
lean_object* v_fvarId_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_958_; 
v_fvarId_941_ = lean_ctor_get(v_e_690_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_e_690_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_e_690_, 0);
lean_dec(v_unused_959_);
v___x_943_ = v_e_690_;
v_isShared_944_ = v_isSharedCheck_958_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_fvarId_941_);
lean_dec(v_e_690_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_958_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_941_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 5);
lean_ctor_set(v___x_943_, 1, v_a_946_);
lean_ctor_set(v___x_943_, 0, v___x_950_);
v___x_952_ = v___x_943_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_a_946_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_952_);
v___x_954_ = v___x_948_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_del_object(v___x_943_);
return v___x_945_;
}
}
}
case 14:
{
lean_object* v_fvarId_960_; lean_object* v___x_961_; 
v_fvarId_960_ = lean_ctor_get(v_e_690_, 0);
lean_inc(v_fvarId_960_);
lean_dec_ref_known(v_e_690_, 1);
v___x_961_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_960_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_a_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
return v___x_961_;
}
}
default: 
{
lean_object* v_fvarId_972_; lean_object* v___x_973_; 
v_fvarId_972_ = lean_ctor_get(v_e_690_, 0);
lean_inc(v_fvarId_972_);
lean_dec_ref_known(v_e_690_, 1);
v___x_973_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_972_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_983_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_983_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_978_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_a_974_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_984_, lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
uint8_t v_pu_boxed_992_; lean_object* v_res_993_; 
v_pu_boxed_992_ = lean_unbox(v_pu_984_);
v_res_993_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_992_, v_e_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec_ref(v_a_986_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_binderName_1003_; lean_object* v_type_1004_; uint8_t v_borrow_1005_; lean_object* v___y_1007_; 
v_binderName_1003_ = lean_ctor_get(v_param_998_, 1);
lean_inc(v_binderName_1003_);
v_type_1004_ = lean_ctor_get(v_param_998_, 2);
lean_inc_ref(v_type_1004_);
v_borrow_1005_ = lean_ctor_get_uint8(v_param_998_, sizeof(void*)*3);
lean_dec_ref(v_param_998_);
if (v_borrow_1005_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1007_ = v___x_1040_;
goto v___jp_1006_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_1007_ = v___x_1041_;
goto v___jp_1006_;
}
v___jp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1000_);
v___x_1009_ = l_Lean_pp_funBinderTypes;
v___x_1010_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1008_, v___x_1009_);
lean_dec_ref(v___x_1008_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_type_1004_);
v___x_1011_ = 1;
v___x_1012_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_1003_, v___x_1011_);
lean_inc_ref(v___y_1007_);
v___x_1013_ = lean_string_append(v___y_1007_, v___x_1012_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1004_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1039_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1021_ = l_Lean_Name_toString(v_binderName_1003_, v___x_1010_);
v___x_1022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
lean_inc_ref(v___y_1007_);
v___x_1025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___y_1007_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_a_1017_);
v___x_1028_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1029_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
v___x_1031_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1028_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = 0;
v___x_1035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1035_);
v___x_1037_ = v___x_1019_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_dec(v_binderName_1003_);
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec_ref(v_a_1043_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1048_, lean_object* v_param_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1049_, v_a_1050_, v_a_1053_, v_a_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1057_, lean_object* v_param_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint8_t v_pu_boxed_1065_; lean_object* v_res_1066_; 
v_pu_boxed_1065_ = lean_unbox(v_pu_1057_);
v_res_1066_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1065_, v_param_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1067_, lean_object* v_params_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1076_ = lean_box(v_pu_1067_);
v___x_1077_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1075_, v_params_1068_, v___x_1077_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1079_, lean_object* v_params_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
uint8_t v_pu_boxed_1087_; lean_object* v_res_1088_; 
v_pu_boxed_1087_ = lean_unbox(v_pu_1079_);
v_res_1088_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1087_, v_params_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec_ref(v_params_1080_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1095_, lean_object* v_letDecl_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1100_);
v___x_1104_ = l_Lean_pp_letVarTypes;
v___x_1105_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1103_, v___x_1104_);
lean_dec_ref(v___x_1103_);
if (v___x_1105_ == 0)
{
lean_object* v_binderName_1106_; lean_object* v_value_1107_; lean_object* v___x_1108_; 
v_binderName_1106_ = lean_ctor_get(v_letDecl_1096_, 1);
lean_inc(v_binderName_1106_);
v_value_1107_ = lean_ctor_get(v_letDecl_1096_, 3);
lean_inc(v_value_1107_);
lean_dec_ref(v_letDecl_1096_);
v___x_1108_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1095_, v_value_1107_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1114_ = 1;
v___x_1115_ = l_Lean_Name_toString(v_binderName_1106_, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1113_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_dec(v_binderName_1106_);
return v___x_1108_;
}
}
else
{
lean_object* v_binderName_1125_; lean_object* v_type_1126_; lean_object* v_value_1127_; lean_object* v___x_1128_; 
v_binderName_1125_ = lean_ctor_get(v_letDecl_1096_, 1);
lean_inc(v_binderName_1125_);
v_type_1126_ = lean_ctor_get(v_letDecl_1096_, 2);
lean_inc_ref(v_type_1126_);
v_value_1127_ = lean_ctor_get(v_letDecl_1096_, 3);
lean_inc(v_value_1127_);
lean_dec_ref(v_letDecl_1096_);
v___x_1128_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1126_, v_a_1097_, v_a_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1154_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1154_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1154_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1095_, v_value_1127_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1153_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1153_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1153_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1139_ = l_Lean_Name_toString(v_binderName_1125_, v___x_1105_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 3);
lean_ctor_set(v___x_1131_, 0, v___x_1139_);
v___x_1141_ = v___x_1131_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1138_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_a_1129_);
v___x_1146_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1148_);
v___x_1150_ = v___x_1136_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_del_object(v___x_1131_);
lean_dec(v_a_1129_);
lean_dec(v_binderName_1125_);
return v___x_1133_;
}
}
}
else
{
lean_dec(v_value_1127_);
lean_dec(v_binderName_1125_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* v_pu_1155_, lean_object* v_letDecl_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v_pu_boxed_1163_; lean_object* v_res_1164_; 
v_pu_boxed_1163_ = lean_unbox(v_pu_1155_);
v_res_1164_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_boxed_1163_, v_letDecl_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_bs_1167_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1168_ == 0)
{
return v_bs_1167_;
}
else
{
lean_object* v_v_1169_; lean_object* v_fvarId_1170_; lean_object* v___x_1171_; lean_object* v_bs_x27_1172_; lean_object* v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_v_1169_ = lean_array_uget_borrowed(v_bs_1167_, v_i_1166_);
v_fvarId_1170_ = lean_ctor_get(v_v_1169_, 0);
lean_inc(v_fvarId_1170_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v_bs_x27_1172_ = lean_array_uset(v_bs_1167_, v_i_1166_, v___x_1171_);
v___x_1173_ = l_Lean_mkFVar(v_fvarId_1170_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1166_, v___x_1174_);
v___x_1176_ = lean_array_uset(v_bs_x27_1172_, v_i_1166_, v___x_1173_);
v_i_1166_ = v___x_1175_;
v_bs_1167_ = v___x_1176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1178_, lean_object* v_i_1179_, lean_object* v_bs_1180_){
_start:
{
size_t v_sz_boxed_1181_; size_t v_i_boxed_1182_; lean_object* v_res_1183_; 
v_sz_boxed_1181_ = lean_unbox_usize(v_sz_1178_);
lean_dec(v_sz_1178_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1181_, v_i_boxed_1182_, v_bs_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1184_, lean_object* v_ps_1185_, lean_object* v_type_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Lean_Expr_isErased(v_type_1186_);
if (v___x_1190_ == 0)
{
if (v_pu_1184_ == 0)
{
size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_sz_1191_ = lean_array_size(v_ps_1185_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1191_, v___x_1192_, v_ps_1185_);
v___x_1194_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1186_, v___x_1193_, v_a_1187_, v_a_1188_);
lean_dec_ref(v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; 
lean_dec_ref(v_ps_1185_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_type_1186_);
return v___x_1195_;
}
}
else
{
lean_object* v___x_1196_; 
lean_dec_ref(v_ps_1185_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_type_1186_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1197_, lean_object* v_ps_1198_, lean_object* v_type_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v_pu_boxed_1203_; lean_object* v_res_1204_; 
v_pu_boxed_1203_ = lean_unbox(v_pu_1197_);
v_res_1204_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1203_, v_ps_1198_, v_type_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1229_, lean_object* v_alt_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
switch(lean_obj_tag(v_alt_1230_))
{
case 0:
{
lean_object* v_ctorName_1237_; lean_object* v_params_1238_; lean_object* v_code_1239_; lean_object* v___x_1240_; 
v_ctorName_1237_ = lean_ctor_get(v_alt_1230_, 0);
lean_inc(v_ctorName_1237_);
v_params_1238_ = lean_ctor_get(v_alt_1230_, 1);
lean_inc_ref(v_params_1238_);
v_code_1239_ = lean_ctor_get(v_alt_1230_, 2);
lean_inc_ref(v_code_1239_);
lean_dec_ref_known(v_alt_1230_, 3);
v___x_1240_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1229_, v_params_1238_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec_ref(v_params_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1266_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1266_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1266_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1229_, v_code_1239_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1265_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1250_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1251_ = 1;
v___x_1252_ = l_Lean_Name_toString(v_ctorName_1237_, v___x_1251_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 3);
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1250_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_a_1241_);
v___x_1257_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_Std_Format_indentD(v_a_1246_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1260_);
v___x_1262_ = v___x_1248_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_del_object(v___x_1243_);
lean_dec(v_a_1241_);
lean_dec(v_ctorName_1237_);
return v___x_1245_;
}
}
}
else
{
lean_dec_ref(v_code_1239_);
lean_dec(v_ctorName_1237_);
return v___x_1240_;
}
}
case 1:
{
lean_object* v_info_1267_; lean_object* v_code_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1293_; 
v_info_1267_ = lean_ctor_get(v_alt_1230_, 0);
v_code_1268_ = lean_ctor_get(v_alt_1230_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_alt_1230_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1270_ = v_alt_1230_;
v_isShared_1271_ = v_isSharedCheck_1293_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_code_1268_);
lean_inc(v_info_1267_);
lean_dec(v_alt_1230_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1293_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1229_, v_code_1268_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1292_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_name_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v_name_1277_ = lean_ctor_get(v_info_1267_, 0);
lean_inc(v_name_1277_);
lean_dec_ref(v_info_1267_);
v___x_1278_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1279_ = 1;
v___x_1280_ = l_Lean_Name_toString(v_name_1277_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 5);
lean_ctor_set(v___x_1270_, 1, v___x_1281_);
lean_ctor_set(v___x_1270_, 0, v___x_1278_);
v___x_1283_ = v___x_1270_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1284_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Std_Format_indentD(v_a_1273_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1287_);
v___x_1289_ = v___x_1275_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_del_object(v___x_1270_);
lean_dec_ref(v_info_1267_);
return v___x_1272_;
}
}
}
default: 
{
lean_object* v_code_1294_; lean_object* v___x_1295_; 
v_code_1294_ = lean_ctor_get(v_alt_1230_, 0);
lean_inc_ref(v_code_1294_);
lean_dec_ref_known(v_alt_1230_, 1);
v___x_1295_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1229_, v_code_1294_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1306_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1306_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1306_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1300_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1301_ = l_Std_Format_indentD(v_a_1296_);
v___x_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1302_);
v___x_1304_ = v___x_1298_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
else
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1307_, lean_object* v_alt_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_pu_boxed_1315_; lean_object* v_res_1316_; 
v_pu_boxed_1315_ = lean_unbox(v_pu_1307_);
v_res_1316_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1315_, v_alt_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1368_, lean_object* v_c_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
switch(lean_obj_tag(v_c_1369_))
{
case 0:
{
lean_object* v_decl_1376_; lean_object* v_k_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1399_; 
v_decl_1376_ = lean_ctor_get(v_c_1369_, 0);
v_k_1377_ = lean_ctor_get(v_c_1369_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1379_ = v_c_1369_;
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_k_1377_);
lean_inc(v_decl_1376_);
lean_dec(v_c_1369_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1368_, v_decl_1376_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1377_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1398_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 5);
lean_ctor_set(v___x_1379_, 1, v___x_1388_);
lean_ctor_set(v___x_1379_, 0, v_a_1382_);
v___x_1390_ = v___x_1379_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1382_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1391_ = lean_box(1);
v___x_1392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1393_);
v___x_1395_ = v___x_1386_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_dec(v_a_1382_);
lean_del_object(v___x_1379_);
return v___x_1383_;
}
}
else
{
lean_del_object(v___x_1379_);
lean_dec_ref(v_k_1377_);
return v___x_1381_;
}
}
}
case 1:
{
lean_object* v_decl_1400_; lean_object* v_k_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_decl_1400_ = lean_ctor_get(v_c_1369_, 0);
v_k_1401_ = lean_ctor_get(v_c_1369_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v_c_1369_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_k_1401_);
lean_inc(v_decl_1400_);
lean_dec(v_c_1369_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1368_, v_decl_1400_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1401_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1424_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 5);
lean_ctor_set(v___x_1403_, 1, v_a_1406_);
lean_ctor_set(v___x_1403_, 0, v___x_1412_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1406_);
v___x_1414_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1415_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_box(1);
v___x_1418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1419_);
v___x_1421_ = v___x_1410_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_dec(v_a_1406_);
lean_del_object(v___x_1403_);
return v___x_1407_;
}
}
else
{
lean_del_object(v___x_1403_);
lean_dec_ref(v_k_1401_);
return v___x_1405_;
}
}
}
case 2:
{
lean_object* v_decl_1426_; lean_object* v_k_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1451_; 
v_decl_1426_ = lean_ctor_get(v_c_1369_, 0);
v_k_1427_ = lean_ctor_get(v_c_1369_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1429_ = v_c_1369_;
v_isShared_1430_ = v_isSharedCheck_1451_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_k_1427_);
lean_inc(v_decl_1426_);
lean_dec(v_c_1369_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1451_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1368_, v_decl_1426_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1427_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1450_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1450_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1450_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 5);
lean_ctor_set(v___x_1429_, 1, v_a_1432_);
lean_ctor_set(v___x_1429_, 0, v___x_1438_);
v___x_1440_ = v___x_1429_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_a_1432_);
v___x_1440_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1441_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_box(1);
v___x_1444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v_a_1434_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1445_);
v___x_1447_ = v___x_1436_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_dec(v_a_1432_);
lean_del_object(v___x_1429_);
return v___x_1433_;
}
}
else
{
lean_del_object(v___x_1429_);
lean_dec_ref(v_k_1427_);
return v___x_1431_;
}
}
}
case 3:
{
lean_object* v_fvarId_1452_; lean_object* v_args_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1473_; 
v_fvarId_1452_ = lean_ctor_get(v_c_1369_, 0);
v_args_1453_ = lean_ctor_get(v_c_1369_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1455_ = v_c_1369_;
v_isShared_1456_ = v_isSharedCheck_1473_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_args_1453_);
lean_inc(v_fvarId_1452_);
lean_dec(v_c_1369_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1473_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1452_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1368_, v_args_1453_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec_ref(v_args_1453_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1472_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 5);
lean_ctor_set(v___x_1455_, 1, v_a_1458_);
lean_ctor_set(v___x_1455_, 0, v___x_1464_);
v___x_1466_ = v___x_1455_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_a_1458_);
v___x_1466_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_a_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1467_);
v___x_1469_ = v___x_1462_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_dec(v_a_1458_);
lean_del_object(v___x_1455_);
return v___x_1459_;
}
}
else
{
lean_del_object(v___x_1455_);
lean_dec_ref(v_args_1453_);
return v___x_1457_;
}
}
}
case 4:
{
lean_object* v_cases_1474_; lean_object* v_resultType_1475_; lean_object* v_discr_1476_; lean_object* v_alts_1477_; lean_object* v___x_1478_; 
v_cases_1474_ = lean_ctor_get(v_c_1369_, 0);
lean_inc_ref(v_cases_1474_);
lean_dec_ref_known(v_c_1369_, 1);
v_resultType_1475_ = lean_ctor_get(v_cases_1474_, 1);
lean_inc_ref(v_resultType_1475_);
v_discr_1476_ = lean_ctor_get(v_cases_1474_, 2);
lean_inc(v_discr_1476_);
v_alts_1477_ = lean_ctor_get(v_cases_1474_, 3);
lean_inc_ref(v_alts_1477_);
lean_dec_ref(v_cases_1474_);
v___x_1478_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1476_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1475_, v_a_1370_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = lean_box(1);
v___x_1483_ = lean_box(v_pu_1368_);
v___x_1484_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1482_, v_alts_1477_, v___x_1484_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec_ref(v_alts_1477_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1499_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1499_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1499_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1490_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_a_1479_);
v___x_1492_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_a_1481_);
v___x_1495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1495_);
v___x_1497_ = v___x_1488_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_dec(v_a_1481_);
lean_dec(v_a_1479_);
return v___x_1485_;
}
}
else
{
lean_dec(v_a_1479_);
lean_dec_ref(v_alts_1477_);
return v___x_1480_;
}
}
else
{
lean_dec_ref(v_alts_1477_);
lean_dec_ref(v_resultType_1475_);
return v___x_1478_;
}
}
case 5:
{
lean_object* v_fvarId_1500_; lean_object* v___x_1501_; 
v_fvarId_1500_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1500_);
lean_dec_ref_known(v_c_1369_, 1);
v___x_1501_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1500_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1511_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_a_1502_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1507_);
v___x_1509_ = v___x_1504_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
return v___x_1501_;
}
}
case 6:
{
lean_object* v_type_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1534_; 
v_type_1512_ = lean_ctor_get(v_c_1369_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1514_ = v_c_1369_;
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_type_1512_);
lean_dec(v_c_1369_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1373_);
v___x_1517_ = l_Lean_pp_all;
v___x_1518_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1516_, v___x_1517_);
lean_dec_ref(v___x_1516_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_dec_ref(v_type_1512_);
v___x_1519_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1519_);
v___x_1521_ = v___x_1514_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
else
{
lean_object* v___x_1523_; 
lean_del_object(v___x_1514_);
v___x_1523_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1512_, v_a_1370_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1528_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
return v___x_1523_;
}
}
}
}
case 7:
{
lean_object* v_fvarId_1535_; lean_object* v_i_1536_; lean_object* v_y_1537_; lean_object* v_k_1538_; lean_object* v___x_1539_; 
v_fvarId_1535_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1535_);
v_i_1536_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_i_1536_);
v_y_1537_ = lean_ctor_get(v_c_1369_, 2);
lean_inc(v_y_1537_);
v_k_1538_ = lean_ctor_get(v_c_1369_, 3);
lean_inc_ref(v_k_1538_);
lean_dec_ref_known(v_c_1369_, 4);
v___x_1539_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1535_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1537_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1572_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1572_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1572_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1538_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1571_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1571_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1571_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1551_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v_a_1540_);
v___x_1553_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Nat_reprFast(v_i_1536_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 3);
lean_ctor_set(v___x_1544_, 0, v___x_1555_);
v___x_1557_ = v___x_1544_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1554_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_a_1542_);
v___x_1562_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_box(1);
v___x_1565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1547_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1566_);
v___x_1568_ = v___x_1549_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_del_object(v___x_1544_);
lean_dec(v_a_1542_);
lean_dec(v_a_1540_);
lean_dec(v_i_1536_);
return v___x_1546_;
}
}
}
else
{
lean_dec(v_a_1540_);
lean_dec_ref(v_k_1538_);
lean_dec(v_i_1536_);
return v___x_1541_;
}
}
else
{
lean_dec_ref(v_k_1538_);
lean_dec(v_y_1537_);
lean_dec(v_i_1536_);
return v___x_1539_;
}
}
case 8:
{
lean_object* v_fvarId_1573_; lean_object* v_i_1574_; lean_object* v_y_1575_; lean_object* v_k_1576_; lean_object* v___x_1577_; 
v_fvarId_1573_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1573_);
v_i_1574_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_i_1574_);
v_y_1575_ = lean_ctor_get(v_c_1369_, 2);
lean_inc(v_y_1575_);
v_k_1576_ = lean_ctor_get(v_c_1369_, 3);
lean_inc_ref(v_k_1576_);
lean_dec_ref_known(v_c_1369_, 4);
v___x_1577_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1573_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1575_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1610_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1576_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1609_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1589_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v_a_1578_);
v___x_1591_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Nat_reprFast(v_i_1574_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 3);
lean_ctor_set(v___x_1582_, 0, v___x_1593_);
v___x_1595_ = v___x_1582_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1592_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v_a_1580_);
v___x_1600_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_box(1);
v___x_1603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1604_);
v___x_1606_ = v___x_1587_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_del_object(v___x_1582_);
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_dec(v_i_1574_);
return v___x_1584_;
}
}
}
else
{
lean_dec(v_a_1578_);
lean_dec_ref(v_k_1576_);
lean_dec(v_i_1574_);
return v___x_1579_;
}
}
else
{
lean_dec_ref(v_k_1576_);
lean_dec(v_y_1575_);
lean_dec(v_i_1574_);
return v___x_1577_;
}
}
case 9:
{
lean_object* v_fvarId_1611_; lean_object* v_i_1612_; lean_object* v_offset_1613_; lean_object* v_y_1614_; lean_object* v_ty_1615_; lean_object* v_k_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_fvarId_1611_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1611_);
v_i_1612_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_i_1612_);
v_offset_1613_ = lean_ctor_get(v_c_1369_, 2);
lean_inc(v_offset_1613_);
v_y_1614_ = lean_ctor_get(v_c_1369_, 3);
lean_inc(v_y_1614_);
v_ty_1615_ = lean_ctor_get(v_c_1369_, 4);
lean_inc_ref(v_ty_1615_);
v_k_1616_ = lean_ctor_get(v_c_1369_, 5);
lean_inc_ref(v_k_1616_);
lean_dec_ref_known(v_c_1369_, 6);
v___x_1617_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1373_);
v___x_1618_ = l_Lean_pp_letVarTypes;
v___x_1619_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1617_, v___x_1618_);
lean_dec_ref(v___x_1617_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v_ty_1615_);
v___x_1620_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1611_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1664_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1664_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1664_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1614_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1663_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1663_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1663_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1616_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1662_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1662_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1662_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1635_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_a_1621_);
v___x_1637_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Nat_reprFast(v_i_1612_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 3);
lean_ctor_set(v___x_1628_, 0, v___x_1639_);
v___x_1641_ = v___x_1628_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1638_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Nat_reprFast(v_offset_1613_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 3);
lean_ctor_set(v___x_1623_, 0, v___x_1645_);
v___x_1647_ = v___x_1623_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1644_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1626_);
v___x_1652_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_box(1);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1656_);
v___x_1658_ = v___x_1633_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
else
{
lean_del_object(v___x_1628_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1630_;
}
}
}
else
{
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
lean_dec_ref(v_k_1616_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1625_;
}
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec(v_y_1614_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1611_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1615_, v_a_1370_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1714_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1714_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1714_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1614_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1713_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1713_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1713_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1616_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1712_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1682_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v_a_1666_);
v___x_1684_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Nat_reprFast(v_i_1612_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 3);
lean_ctor_set(v___x_1675_, 0, v___x_1686_);
v___x_1688_ = v___x_1675_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1685_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Nat_reprFast(v_offset_1613_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 3);
lean_ctor_set(v___x_1670_, 0, v___x_1692_);
v___x_1694_ = v___x_1670_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1691_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v_a_1668_);
v___x_1699_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_a_1673_);
v___x_1702_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_box(1);
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1706_);
v___x_1708_ = v___x_1680_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_del_object(v___x_1675_);
lean_dec(v_a_1673_);
lean_del_object(v___x_1670_);
lean_dec(v_a_1668_);
lean_dec(v_a_1666_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1677_;
}
}
}
else
{
lean_del_object(v___x_1670_);
lean_dec(v_a_1668_);
lean_dec(v_a_1666_);
lean_dec_ref(v_k_1616_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1672_;
}
}
}
else
{
lean_dec(v_a_1666_);
lean_dec_ref(v_k_1616_);
lean_dec(v_y_1614_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1667_;
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_ty_1615_);
lean_dec(v_y_1614_);
lean_dec(v_offset_1613_);
lean_dec(v_i_1612_);
return v___x_1665_;
}
}
}
case 10:
{
lean_object* v_fvarId_1715_; lean_object* v_cidx_1716_; lean_object* v_k_1717_; lean_object* v___x_1718_; 
v_fvarId_1715_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1715_);
v_cidx_1716_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_cidx_1716_);
v_k_1717_ = lean_ctor_get(v_c_1369_, 2);
lean_inc_ref(v_k_1717_);
lean_dec_ref_known(v_c_1369_, 3);
v___x_1718_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1715_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1746_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1746_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1746_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1717_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1745_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1745_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1745_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1728_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1719_);
v___x_1730_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Nat_reprFast(v_cidx_1716_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 3);
lean_ctor_set(v___x_1721_, 0, v___x_1732_);
v___x_1734_ = v___x_1721_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1731_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_box(1);
v___x_1739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v_a_1724_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1740_);
v___x_1742_ = v___x_1726_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_del_object(v___x_1721_);
lean_dec(v_a_1719_);
lean_dec(v_cidx_1716_);
return v___x_1723_;
}
}
}
else
{
lean_dec_ref(v_k_1717_);
lean_dec(v_cidx_1716_);
return v___x_1718_;
}
}
case 11:
{
lean_object* v_fvarId_1747_; lean_object* v_n_1748_; uint8_t v_check_1749_; uint8_t v_persistent_1750_; lean_object* v_k_1751_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1820_; 
v_fvarId_1747_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1747_);
v_n_1748_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_n_1748_);
v_check_1749_ = lean_ctor_get_uint8(v_c_1369_, sizeof(void*)*3);
v_persistent_1750_ = lean_ctor_get_uint8(v_c_1369_, sizeof(void*)*3 + 1);
v_k_1751_ = lean_ctor_get(v_c_1369_, 2);
lean_inc_ref(v_k_1751_);
lean_dec_ref_known(v_c_1369_, 3);
if (v_persistent_1750_ == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1820_ = v___x_1823_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___y_1820_ = v___x_1824_;
goto v___jp_1819_;
}
v___jp_1752_:
{
lean_object* v_ann_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
lean_inc_ref(v___y_1753_);
v_ann_1755_ = lean_string_append(v___y_1753_, v___y_1754_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_dec_eq(v_n_1748_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1747_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1790_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1790_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1790_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1751_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1789_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1769_ = l_Nat_reprFast(v_n_1748_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 3);
lean_ctor_set(v___x_1761_, 0, v___x_1769_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1768_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_ann_1755_);
v___x_1776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_a_1759_);
v___x_1780_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_box(1);
v___x_1783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_a_1764_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1784_);
v___x_1786_ = v___x_1766_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_del_object(v___x_1761_);
lean_dec(v_a_1759_);
lean_dec_ref(v_ann_1755_);
lean_dec(v_n_1748_);
return v___x_1763_;
}
}
}
else
{
lean_dec_ref(v_ann_1755_);
lean_dec_ref(v_k_1751_);
lean_dec(v_n_1748_);
return v___x_1758_;
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_n_1748_);
v___x_1791_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1747_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1818_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1818_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1818_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1751_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1817_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 3);
lean_ctor_set(v___x_1794_, 0, v_ann_1755_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_ann_1755_);
v___x_1803_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1801_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_a_1792_);
v___x_1808_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_box(1);
v___x_1811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_a_1797_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1812_);
v___x_1814_ = v___x_1799_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_del_object(v___x_1794_);
lean_dec(v_a_1792_);
lean_dec_ref(v_ann_1755_);
return v___x_1796_;
}
}
}
else
{
lean_dec_ref(v_ann_1755_);
lean_dec_ref(v_k_1751_);
return v___x_1791_;
}
}
}
v___jp_1819_:
{
if (v_check_1749_ == 0)
{
lean_object* v___x_1821_; 
v___x_1821_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
v___y_1753_ = v___y_1820_;
v___y_1754_ = v___x_1821_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1753_ = v___y_1820_;
v___y_1754_ = v___x_1822_;
goto v___jp_1752_;
}
}
}
case 12:
{
lean_object* v_fvarId_1825_; lean_object* v_n_1826_; uint8_t v_check_1827_; uint8_t v_persistent_1828_; lean_object* v_objs_x3f_1829_; lean_object* v_k_1830_; lean_object* v_ann_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v_ann_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v_ann_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; 
v_fvarId_1825_ = lean_ctor_get(v_c_1369_, 0);
lean_inc(v_fvarId_1825_);
v_n_1826_ = lean_ctor_get(v_c_1369_, 1);
lean_inc(v_n_1826_);
v_check_1827_ = lean_ctor_get_uint8(v_c_1369_, sizeof(void*)*4);
v_persistent_1828_ = lean_ctor_get_uint8(v_c_1369_, sizeof(void*)*4 + 1);
v_objs_x3f_1829_ = lean_ctor_get(v_c_1369_, 2);
lean_inc(v_objs_x3f_1829_);
v_k_1830_ = lean_ctor_get(v_c_1369_, 3);
lean_inc_ref(v_k_1830_);
lean_dec_ref_known(v_c_1369_, 4);
if (v_persistent_1828_ == 0)
{
lean_object* v_ann_1924_; 
v_ann_1924_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v_ann_1916_ = v_ann_1924_;
v___y_1917_ = v_a_1370_;
v___y_1918_ = v_a_1371_;
v___y_1919_ = v_a_1372_;
v___y_1920_ = v_a_1373_;
v___y_1921_ = v_a_1374_;
goto v___jp_1915_;
}
else
{
lean_object* v_ann_1925_; 
v_ann_1925_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v_ann_1916_ = v_ann_1925_;
v___y_1917_ = v_a_1370_;
v___y_1918_ = v_a_1371_;
v___y_1919_ = v_a_1372_;
v___y_1920_ = v_a_1373_;
v___y_1921_ = v_a_1374_;
goto v___jp_1915_;
}
v___jp_1831_:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_dec_eq(v_n_1826_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1825_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1872_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1872_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1872_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1830_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1871_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1871_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1871_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1851_ = l_Nat_reprFast(v_n_1826_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 3);
lean_ctor_set(v___x_1843_, 0, v___x_1851_);
v___x_1853_ = v___x_1843_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_ann_1832_);
v___x_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_a_1841_);
v___x_1862_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_box(1);
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v_a_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1866_);
v___x_1868_ = v___x_1848_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_del_object(v___x_1843_);
lean_dec(v_a_1841_);
lean_dec_ref(v_ann_1832_);
lean_dec(v_n_1826_);
return v___x_1845_;
}
}
}
else
{
lean_dec_ref(v_ann_1832_);
lean_dec_ref(v_k_1830_);
lean_dec(v_n_1826_);
return v___x_1840_;
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_n_1826_);
v___x_1873_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1825_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1900_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1900_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1900_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1830_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1899_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1899_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1899_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 3);
lean_ctor_set(v___x_1876_, 0, v_ann_1832_);
v___x_1885_ = v___x_1876_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_ann_1832_);
v___x_1885_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1883_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_a_1874_);
v___x_1890_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_box(1);
v___x_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v_a_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1894_);
v___x_1896_ = v___x_1881_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_del_object(v___x_1876_);
lean_dec(v_a_1874_);
lean_dec_ref(v_ann_1832_);
return v___x_1878_;
}
}
}
else
{
lean_dec_ref(v_ann_1832_);
lean_dec_ref(v_k_1830_);
return v___x_1873_;
}
}
}
v___jp_1901_:
{
if (lean_obj_tag(v_objs_x3f_1829_) == 1)
{
lean_object* v_val_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_ann_1914_; 
v_val_1908_ = lean_ctor_get(v_objs_x3f_1829_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v_objs_x3f_1829_, 1);
v___x_1909_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0));
v___x_1910_ = l_Nat_reprFast(v_val_1908_);
v___x_1911_ = lean_string_append(v___x_1909_, v___x_1910_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__40));
v___x_1913_ = lean_string_append(v___x_1911_, v___x_1912_);
v_ann_1914_ = lean_string_append(v_ann_1902_, v___x_1913_);
lean_dec_ref(v___x_1913_);
v_ann_1832_ = v_ann_1914_;
v___y_1833_ = v___y_1903_;
v___y_1834_ = v___y_1904_;
v___y_1835_ = v___y_1905_;
v___y_1836_ = v___y_1906_;
v___y_1837_ = v___y_1907_;
goto v___jp_1831_;
}
else
{
lean_dec(v_objs_x3f_1829_);
v_ann_1832_ = v_ann_1902_;
v___y_1833_ = v___y_1903_;
v___y_1834_ = v___y_1904_;
v___y_1835_ = v___y_1905_;
v___y_1836_ = v___y_1906_;
v___y_1837_ = v___y_1907_;
goto v___jp_1831_;
}
}
v___jp_1915_:
{
if (v_check_1827_ == 0)
{
lean_object* v___x_1922_; lean_object* v_ann_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
lean_inc_ref(v_ann_1916_);
v_ann_1923_ = lean_string_append(v_ann_1916_, v___x_1922_);
v_ann_1902_ = v_ann_1923_;
v___y_1903_ = v___y_1917_;
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1919_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
goto v___jp_1901_;
}
else
{
lean_inc_ref(v_ann_1916_);
v_ann_1902_ = v_ann_1916_;
v___y_1903_ = v___y_1917_;
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1919_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
goto v___jp_1901_;
}
}
}
default: 
{
lean_object* v_fvarId_1926_; lean_object* v_k_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1951_; 
v_fvarId_1926_ = lean_ctor_get(v_c_1369_, 0);
v_k_1927_ = lean_ctor_get(v_c_1369_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_c_1369_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1929_ = v_c_1369_;
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_k_1927_);
lean_inc(v_fvarId_1926_);
lean_dec(v_c_1369_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1926_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1368_, v_k_1927_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1950_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1950_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1950_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__42));
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 5);
lean_ctor_set(v___x_1929_, 1, v_a_1932_);
lean_ctor_set(v___x_1929_, 0, v___x_1938_);
v___x_1940_ = v___x_1929_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_a_1932_);
v___x_1940_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_box(1);
v___x_1944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1945_);
v___x_1947_ = v___x_1936_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_dec(v_a_1932_);
lean_del_object(v___x_1929_);
return v___x_1933_;
}
}
else
{
lean_del_object(v___x_1929_);
lean_dec_ref(v_k_1927_);
return v___x_1931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1952_, lean_object* v_funDecl_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_binderName_1960_; lean_object* v_params_1961_; lean_object* v_type_1962_; lean_object* v_value_1963_; lean_object* v___x_1964_; 
v_binderName_1960_ = lean_ctor_get(v_funDecl_1953_, 1);
lean_inc(v_binderName_1960_);
v_params_1961_ = lean_ctor_get(v_funDecl_1953_, 2);
lean_inc_ref(v_params_1961_);
v_type_1962_ = lean_ctor_get(v_funDecl_1953_, 3);
lean_inc_ref(v_type_1962_);
v_value_1963_ = lean_ctor_get(v_funDecl_1953_, 4);
lean_inc_ref(v_value_1963_);
lean_dec_ref(v_funDecl_1953_);
v___x_1964_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1952_, v_params_1961_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1952_, v_params_1961_, v_type_1962_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1967_, v_a_1954_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1995_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1995_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1995_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1952_, v_value_1963_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1994_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1994_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1994_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1978_ = 1;
v___x_1979_ = l_Lean_Name_toString(v_binderName_1960_, v___x_1978_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 3);
lean_ctor_set(v___x_1971_, 0, v___x_1979_);
v___x_1981_ = v___x_1971_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_a_1965_);
v___x_1983_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v_a_1969_);
v___x_1986_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = l_Std_Format_indentD(v_a_1974_);
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1989_);
v___x_1991_ = v___x_1976_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
lean_dec(v_a_1965_);
lean_dec(v_binderName_1960_);
return v___x_1973_;
}
}
}
else
{
lean_dec(v_a_1965_);
lean_dec_ref(v_value_1963_);
lean_dec(v_binderName_1960_);
return v___x_1968_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_a_1965_);
lean_dec_ref(v_value_1963_);
lean_dec(v_binderName_1960_);
v_a_1996_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1966_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1966_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_dec_ref(v_value_1963_);
lean_dec_ref(v_type_1962_);
lean_dec_ref(v_params_1961_);
lean_dec(v_binderName_1960_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_2004_, lean_object* v_funDecl_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
uint8_t v_pu_boxed_2012_; lean_object* v_res_2013_; 
v_pu_boxed_2012_ = lean_unbox(v_pu_2004_);
v_res_2013_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_2012_, v_funDecl_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_2014_, lean_object* v_c_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
uint8_t v_pu_boxed_2022_; lean_object* v_res_2023_; 
v_pu_boxed_2022_ = lean_unbox(v_pu_2014_);
v_res_2023_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_2022_, v_c_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_2027_, lean_object* v_b_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
if (lean_obj_tag(v_b_2028_) == 0)
{
lean_object* v_code_2035_; lean_object* v___x_2036_; 
v_code_2035_ = lean_ctor_get(v_b_2028_, 0);
lean_inc_ref(v_code_2035_);
lean_dec_ref_known(v_b_2028_, 1);
v___x_2036_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_2027_, v_code_2035_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
return v___x_2036_;
}
else
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_isSharedCheck_2044_ = !lean_is_exclusive(v_b_2028_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v_b_2028_, 0);
lean_dec(v_unused_2045_);
v___x_2038_ = v_b_2028_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v_b_2028_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_2046_, lean_object* v_b_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
uint8_t v_pu_boxed_2054_; lean_object* v_res_2055_; 
v_pu_boxed_2054_ = lean_unbox(v_pu_2046_);
v_res_2055_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_2054_, v_b_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_2056_, lean_object* v_opt_2057_){
_start:
{
lean_object* v_name_2058_; lean_object* v_defValue_2059_; lean_object* v_map_2060_; lean_object* v___x_2061_; 
v_name_2058_ = lean_ctor_get(v_opt_2057_, 0);
v_defValue_2059_ = lean_ctor_get(v_opt_2057_, 1);
v_map_2060_ = lean_ctor_get(v_opts_2056_, 0);
v___x_2061_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2060_, v_name_2058_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_inc(v_defValue_2059_);
return v_defValue_2059_;
}
else
{
lean_object* v_val_2062_; 
v_val_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v___x_2061_, 1);
if (lean_obj_tag(v_val_2062_) == 3)
{
lean_object* v_v_2063_; 
v_v_2063_ = lean_ctor_get(v_val_2062_, 0);
lean_inc(v_v_2063_);
lean_dec_ref_known(v_val_2062_, 1);
return v_v_2063_;
}
else
{
lean_dec(v_val_2062_);
lean_inc(v_defValue_2059_);
return v_defValue_2059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_2064_, lean_object* v_opt_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_2064_, v_opt_2065_);
lean_dec_ref(v_opt_2065_);
lean_dec_ref(v_opts_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(lean_object* v_o_2070_, lean_object* v_k_2071_, uint8_t v_v_2072_){
_start:
{
lean_object* v_map_2073_; uint8_t v_hasTrace_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2088_; 
v_map_2073_ = lean_ctor_get(v_o_2070_, 0);
v_hasTrace_2074_ = lean_ctor_get_uint8(v_o_2070_, sizeof(void*)*1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_o_2070_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2076_ = v_o_2070_;
v_isShared_2077_ = v_isSharedCheck_2088_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_map_2073_);
lean_dec(v_o_2070_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2088_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2078_, 0, v_v_2072_);
lean_inc(v_k_2071_);
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2071_, v___x_2078_, v_map_2073_);
if (v_hasTrace_2074_ == 0)
{
lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1));
v___x_2081_ = l_Lean_Name_isPrefixOf(v___x_2080_, v_k_2071_);
lean_dec(v_k_2071_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2079_);
v___x_2083_ = v___x_2076_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2079_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*1, v___x_2081_);
return v___x_2083_;
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v_k_2071_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2079_);
v___x_2086_ = v___x_2076_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2087_, sizeof(void*)*1, v_hasTrace_2074_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___boxed(lean_object* v_o_2089_, lean_object* v_k_2090_, lean_object* v_v_2091_){
_start:
{
uint8_t v_v_boxed_2092_; lean_object* v_res_2093_; 
v_v_boxed_2092_ = lean_unbox(v_v_2091_);
v_res_2093_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_o_2089_, v_k_2090_, v_v_boxed_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_2094_, lean_object* v_opt_2095_, uint8_t v_val_2096_){
_start:
{
lean_object* v_name_2097_; lean_object* v___x_2098_; 
v_name_2097_ = lean_ctor_get(v_opt_2095_, 0);
lean_inc(v_name_2097_);
lean_dec_ref(v_opt_2095_);
v___x_2098_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_opts_2094_, v_name_2097_, v_val_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_2099_, lean_object* v_opt_2100_, lean_object* v_val_2101_){
_start:
{
uint8_t v_val_boxed_2102_; lean_object* v_res_2103_; 
v_val_boxed_2102_ = lean_unbox(v_val_2101_);
v_res_2103_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2099_, v_opt_2100_, v_val_boxed_2102_);
return v_res_2103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_PP_ppExpr_spec__0_spec__0___redArg___closed__0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___y_2115_; uint16_t v___y_2116_; lean_object* v_fileName_2117_; lean_object* v_fileMap_2118_; lean_object* v_currNamespace_2119_; lean_object* v_openDecls_2120_; lean_object* v_initHeartbeats_2121_; lean_object* v_maxHeartbeats_2122_; lean_object* v_quotContext_2123_; lean_object* v_currMacroScope_2124_; lean_object* v_cancelTk_x3f_2125_; lean_object* v_inheritedTraceOptions_2126_; lean_object* v_currRecDepth_2127_; lean_object* v_ref_2128_; uint8_t v_suppressElabErrors_2129_; uint8_t v_checkDeprecated_2130_; uint8_t v_isRecordingDeps_2131_; lean_object* v___y_2132_; lean_object* v_toCold_2152_; lean_object* v_currRecDepth_2153_; lean_object* v_ref_2154_; uint8_t v_suppressElabErrors_2155_; uint8_t v_checkDeprecated_2156_; uint8_t v_isRecordingDeps_2157_; lean_object* v_fileName_2158_; lean_object* v_fileMap_2159_; lean_object* v_options_2160_; lean_object* v_currNamespace_2161_; lean_object* v_openDecls_2162_; lean_object* v_initHeartbeats_2163_; lean_object* v_maxHeartbeats_2164_; lean_object* v_quotContext_2165_; lean_object* v_currMacroScope_2166_; lean_object* v_cancelTk_x3f_2167_; lean_object* v_inheritedTraceOptions_2168_; lean_object* v___y_2170_; uint8_t v___y_2171_; uint16_t v___y_2172_; lean_object* v___y_2195_; 
v_toCold_2152_ = lean_ctor_get(v_a_2111_, 0);
v_currRecDepth_2153_ = lean_ctor_get(v_a_2111_, 1);
v_ref_2154_ = lean_ctor_get(v_a_2111_, 2);
v_suppressElabErrors_2155_ = lean_ctor_get_uint8(v_a_2111_, sizeof(void*)*3 + 2);
v_checkDeprecated_2156_ = lean_ctor_get_uint8(v_a_2111_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2157_ = lean_ctor_get_uint8(v_a_2111_, sizeof(void*)*3 + 4);
v_fileName_2158_ = lean_ctor_get(v_toCold_2152_, 0);
v_fileMap_2159_ = lean_ctor_get(v_toCold_2152_, 1);
v_options_2160_ = lean_ctor_get(v_toCold_2152_, 2);
v_currNamespace_2161_ = lean_ctor_get(v_toCold_2152_, 4);
v_openDecls_2162_ = lean_ctor_get(v_toCold_2152_, 5);
v_initHeartbeats_2163_ = lean_ctor_get(v_toCold_2152_, 6);
v_maxHeartbeats_2164_ = lean_ctor_get(v_toCold_2152_, 7);
v_quotContext_2165_ = lean_ctor_get(v_toCold_2152_, 8);
v_currMacroScope_2166_ = lean_ctor_get(v_toCold_2152_, 9);
v_cancelTk_x3f_2167_ = lean_ctor_get(v_toCold_2152_, 10);
v_inheritedTraceOptions_2168_ = lean_ctor_get(v_toCold_2152_, 11);
if (v_isRecordingDeps_2157_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = l_Lean_pp_sanitizeNames;
lean_inc_ref(v_options_2160_);
v___x_2207_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_options_2160_, v___x_2206_, v_isRecordingDeps_2157_);
v___y_2195_ = v___x_2207_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2208_; 
lean_inc_ref(v_options_2160_);
v___x_2208_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2160_);
v___y_2195_ = v___x_2208_;
goto v___jp_2194_;
}
v___jp_2114_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2133_ = l_Lean_maxRecDepth;
v___x_2134_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v___y_2115_, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2135_, 0, v_fileName_2117_);
lean_ctor_set(v___x_2135_, 1, v_fileMap_2118_);
lean_ctor_set(v___x_2135_, 2, v___y_2115_);
lean_ctor_set(v___x_2135_, 3, v___x_2134_);
lean_ctor_set(v___x_2135_, 4, v_currNamespace_2119_);
lean_ctor_set(v___x_2135_, 5, v_openDecls_2120_);
lean_ctor_set(v___x_2135_, 6, v_initHeartbeats_2121_);
lean_ctor_set(v___x_2135_, 7, v_maxHeartbeats_2122_);
lean_ctor_set(v___x_2135_, 8, v_quotContext_2123_);
lean_ctor_set(v___x_2135_, 9, v_currMacroScope_2124_);
lean_ctor_set(v___x_2135_, 10, v_cancelTk_x3f_2125_);
lean_ctor_set(v___x_2135_, 11, v_inheritedTraceOptions_2126_);
lean_inc(v_ref_2128_);
lean_inc(v_currRecDepth_2127_);
v___x_2136_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v_currRecDepth_2127_);
lean_ctor_set(v___x_2136_, 2, v_ref_2128_);
lean_ctor_set_uint16(v___x_2136_, sizeof(void*)*3, v___y_2116_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*3 + 2, v_suppressElabErrors_2129_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*3 + 3, v_checkDeprecated_2130_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*3 + 4, v_isRecordingDeps_2131_);
v___x_2137_ = lean_st_ref_get(v_a_2110_);
v___x_2138_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2109_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_lctx_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v_lctx_2140_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_lctx_2140_);
lean_dec(v___x_2137_);
v___x_2141_ = lean_unbox(v_a_2139_);
lean_dec(v_a_2139_);
v___x_2142_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2140_, v___x_2141_);
lean_dec_ref(v_lctx_2140_);
lean_inc(v___y_2132_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
v___x_2143_ = lean_apply_6(v_x_2108_, v___x_2142_, v_a_2109_, v_a_2110_, v___x_2136_, v___y_2132_, lean_box(0));
return v___x_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v___x_2137_);
lean_dec_ref_known(v___x_2136_, 3);
lean_dec_ref(v_x_2108_);
v_a_2144_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2138_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2138_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
v___jp_2169_:
{
lean_object* v___x_2173_; lean_object* v_env_2174_; lean_object* v_nextMacroScope_2175_; lean_object* v_ngen_2176_; lean_object* v_auxDeclNGen_2177_; lean_object* v_traceState_2178_; lean_object* v_recordedDeps_2179_; lean_object* v_messages_2180_; lean_object* v_infoState_2181_; lean_object* v_snapshotTasks_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2192_; 
v___x_2173_ = lean_st_ref_take(v_a_2112_);
v_env_2174_ = lean_ctor_get(v___x_2173_, 0);
v_nextMacroScope_2175_ = lean_ctor_get(v___x_2173_, 1);
v_ngen_2176_ = lean_ctor_get(v___x_2173_, 2);
v_auxDeclNGen_2177_ = lean_ctor_get(v___x_2173_, 3);
v_traceState_2178_ = lean_ctor_get(v___x_2173_, 4);
v_recordedDeps_2179_ = lean_ctor_get(v___x_2173_, 6);
v_messages_2180_ = lean_ctor_get(v___x_2173_, 7);
v_infoState_2181_ = lean_ctor_get(v___x_2173_, 8);
v_snapshotTasks_2182_ = lean_ctor_get(v___x_2173_, 9);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v___x_2173_, 5);
lean_dec(v_unused_2193_);
v___x_2184_ = v___x_2173_;
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_snapshotTasks_2182_);
lean_inc(v_infoState_2181_);
lean_inc(v_messages_2180_);
lean_inc(v_recordedDeps_2179_);
lean_inc(v_traceState_2178_);
lean_inc(v_auxDeclNGen_2177_);
lean_inc(v_ngen_2176_);
lean_inc(v_nextMacroScope_2175_);
lean_inc(v_env_2174_);
lean_dec(v___x_2173_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = l_Lean_Kernel_enableDiag(v_env_2174_, v___y_2171_);
v___x_2187_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 5, v___x_2187_);
lean_ctor_set(v___x_2184_, 0, v___x_2186_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_nextMacroScope_2175_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_ngen_2176_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_auxDeclNGen_2177_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_traceState_2178_);
lean_ctor_set(v_reuseFailAlloc_2191_, 5, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2191_, 6, v_recordedDeps_2179_);
lean_ctor_set(v_reuseFailAlloc_2191_, 7, v_messages_2180_);
lean_ctor_set(v_reuseFailAlloc_2191_, 8, v_infoState_2181_);
lean_ctor_set(v_reuseFailAlloc_2191_, 9, v_snapshotTasks_2182_);
v___x_2189_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_st_ref_put(v_a_2112_, v___x_2189_);
lean_inc_ref(v_inheritedTraceOptions_2168_);
lean_inc(v_cancelTk_x3f_2167_);
lean_inc(v_currMacroScope_2166_);
lean_inc(v_quotContext_2165_);
lean_inc(v_maxHeartbeats_2164_);
lean_inc(v_initHeartbeats_2163_);
lean_inc(v_openDecls_2162_);
lean_inc(v_currNamespace_2161_);
lean_inc_ref(v_fileMap_2159_);
lean_inc_ref(v_fileName_2158_);
v___y_2115_ = v___y_2170_;
v___y_2116_ = v___y_2172_;
v_fileName_2117_ = v_fileName_2158_;
v_fileMap_2118_ = v_fileMap_2159_;
v_currNamespace_2119_ = v_currNamespace_2161_;
v_openDecls_2120_ = v_openDecls_2162_;
v_initHeartbeats_2121_ = v_initHeartbeats_2163_;
v_maxHeartbeats_2122_ = v_maxHeartbeats_2164_;
v_quotContext_2123_ = v_quotContext_2165_;
v_currMacroScope_2124_ = v_currMacroScope_2166_;
v_cancelTk_x3f_2125_ = v_cancelTk_x3f_2167_;
v_inheritedTraceOptions_2126_ = v_inheritedTraceOptions_2168_;
v_currRecDepth_2127_ = v_currRecDepth_2153_;
v_ref_2128_ = v_ref_2154_;
v_suppressElabErrors_2129_ = v_suppressElabErrors_2155_;
v_checkDeprecated_2130_ = v_checkDeprecated_2156_;
v_isRecordingDeps_2131_ = v_isRecordingDeps_2157_;
v___y_2132_ = v_a_2112_;
goto v___jp_2114_;
}
}
}
v___jp_2194_:
{
uint16_t v___x_2196_; lean_object* v___x_2197_; lean_object* v_env_2198_; uint8_t v___x_2199_; uint16_t v___x_2200_; uint16_t v___x_2201_; uint16_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2196_ = l_Lean_OptionFlags_ofOptions(v___y_2195_);
v___x_2197_ = lean_st_ref_get(v_a_2112_);
v_env_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc_ref(v_env_2198_);
lean_dec(v___x_2197_);
v___x_2199_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2198_);
lean_dec_ref(v_env_2198_);
v___x_2200_ = 512;
v___x_2201_ = lean_uint16_land(v___x_2196_, v___x_2200_);
v___x_2202_ = 0;
v___x_2203_ = lean_uint16_dec_eq(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
if (v___x_2199_ == 0)
{
uint8_t v___x_2204_; 
v___x_2204_ = 1;
v___y_2170_ = v___y_2195_;
v___y_2171_ = v___x_2204_;
v___y_2172_ = v___x_2196_;
goto v___jp_2169_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2168_);
lean_inc(v_cancelTk_x3f_2167_);
lean_inc(v_currMacroScope_2166_);
lean_inc(v_quotContext_2165_);
lean_inc(v_maxHeartbeats_2164_);
lean_inc(v_initHeartbeats_2163_);
lean_inc(v_openDecls_2162_);
lean_inc(v_currNamespace_2161_);
lean_inc_ref(v_fileMap_2159_);
lean_inc_ref(v_fileName_2158_);
v___y_2115_ = v___y_2195_;
v___y_2116_ = v___x_2196_;
v_fileName_2117_ = v_fileName_2158_;
v_fileMap_2118_ = v_fileMap_2159_;
v_currNamespace_2119_ = v_currNamespace_2161_;
v_openDecls_2120_ = v_openDecls_2162_;
v_initHeartbeats_2121_ = v_initHeartbeats_2163_;
v_maxHeartbeats_2122_ = v_maxHeartbeats_2164_;
v_quotContext_2123_ = v_quotContext_2165_;
v_currMacroScope_2124_ = v_currMacroScope_2166_;
v_cancelTk_x3f_2125_ = v_cancelTk_x3f_2167_;
v_inheritedTraceOptions_2126_ = v_inheritedTraceOptions_2168_;
v_currRecDepth_2127_ = v_currRecDepth_2153_;
v_ref_2128_ = v_ref_2154_;
v_suppressElabErrors_2129_ = v_suppressElabErrors_2155_;
v_checkDeprecated_2130_ = v_checkDeprecated_2156_;
v_isRecordingDeps_2131_ = v_isRecordingDeps_2157_;
v___y_2132_ = v_a_2112_;
goto v___jp_2114_;
}
}
else
{
if (v___x_2199_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2168_);
lean_inc(v_cancelTk_x3f_2167_);
lean_inc(v_currMacroScope_2166_);
lean_inc(v_quotContext_2165_);
lean_inc(v_maxHeartbeats_2164_);
lean_inc(v_initHeartbeats_2163_);
lean_inc(v_openDecls_2162_);
lean_inc(v_currNamespace_2161_);
lean_inc_ref(v_fileMap_2159_);
lean_inc_ref(v_fileName_2158_);
v___y_2115_ = v___y_2195_;
v___y_2116_ = v___x_2196_;
v_fileName_2117_ = v_fileName_2158_;
v_fileMap_2118_ = v_fileMap_2159_;
v_currNamespace_2119_ = v_currNamespace_2161_;
v_openDecls_2120_ = v_openDecls_2162_;
v_initHeartbeats_2121_ = v_initHeartbeats_2163_;
v_maxHeartbeats_2122_ = v_maxHeartbeats_2164_;
v_quotContext_2123_ = v_quotContext_2165_;
v_currMacroScope_2124_ = v_currMacroScope_2166_;
v_cancelTk_x3f_2125_ = v_cancelTk_x3f_2167_;
v_inheritedTraceOptions_2126_ = v_inheritedTraceOptions_2168_;
v_currRecDepth_2127_ = v_currRecDepth_2153_;
v_ref_2128_ = v_ref_2154_;
v_suppressElabErrors_2129_ = v_suppressElabErrors_2155_;
v_checkDeprecated_2130_ = v_checkDeprecated_2156_;
v_isRecordingDeps_2131_ = v_isRecordingDeps_2157_;
v___y_2132_ = v_a_2112_;
goto v___jp_2114_;
}
else
{
uint8_t v___x_2205_; 
v___x_2205_ = 0;
v___y_2170_ = v___y_2195_;
v___y_2171_ = v___x_2205_;
v___y_2172_ = v___x_2196_;
goto v___jp_2169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2216_, lean_object* v_x_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_x_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2224_, v_x_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2232_, lean_object* v_code_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(v_pu_2232_);
v___x_2240_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2240_, 0, v___x_2239_);
lean_closure_set(v___x_2240_, 1, v_code_2233_);
v___x_2241_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2240_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2242_, lean_object* v_code_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
uint8_t v_pu_boxed_2249_; lean_object* v_res_2250_; 
v_pu_boxed_2249_ = lean_unbox(v_pu_2242_);
v_res_2250_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2249_, v_code_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2251_, lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_box(v_pu_2251_);
v___x_2259_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2259_, 0, v___x_2258_);
lean_closure_set(v___x_2259_, 1, v_e_2252_);
v___x_2260_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2259_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2261_, lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v_pu_boxed_2268_; lean_object* v_res_2269_; 
v_pu_boxed_2268_ = lean_unbox(v_pu_2261_);
v_res_2269_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2268_, v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2273_, lean_object* v_params_2274_, lean_object* v_type_2275_, lean_object* v_value_2276_, lean_object* v_name_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2273_, v_params_2274_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2273_, v_params_2274_, v_type_2275_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2287_, v___y_2278_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2317_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2317_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2317_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2273_, v_value_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2316_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2316_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2316_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2298_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2299_ = 1;
v___x_2300_ = l_Lean_Name_toString(v_name_2277_, v___x_2299_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set_tag(v___x_2291_, 3);
lean_ctor_set(v___x_2291_, 0, v___x_2300_);
v___x_2302_ = v___x_2291_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2298_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v_a_2285_);
v___x_2305_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_a_2289_);
v___x_2308_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Std_Format_indentD(v_a_2294_);
v___x_2311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2311_);
v___x_2313_ = v___x_2296_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_del_object(v___x_2291_);
lean_dec(v_a_2289_);
lean_dec(v_a_2285_);
lean_dec(v_name_2277_);
return v___x_2293_;
}
}
}
else
{
lean_dec(v_a_2285_);
lean_dec(v_name_2277_);
lean_dec_ref(v_value_2276_);
return v___x_2288_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2285_);
lean_dec(v_name_2277_);
lean_dec_ref(v_value_2276_);
v_a_2318_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2286_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2286_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_dec(v_name_2277_);
lean_dec_ref(v_value_2276_);
lean_dec_ref(v_type_2275_);
lean_dec_ref(v_params_2274_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2326_, lean_object* v_params_2327_, lean_object* v_type_2328_, lean_object* v_value_2329_, lean_object* v_name_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_pu_boxed_2337_; lean_object* v_res_2338_; 
v_pu_boxed_2337_ = lean_unbox(v_pu_2326_);
v_res_2338_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2337_, v_params_2327_, v_type_2328_, v_value_2329_, v_name_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v___y_2331_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2339_, lean_object* v_decl_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_toSignature_2346_; lean_object* v_value_2347_; lean_object* v_name_2348_; lean_object* v_type_2349_; lean_object* v_params_2350_; lean_object* v___x_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
v_toSignature_2346_ = lean_ctor_get(v_decl_2340_, 0);
lean_inc_ref(v_toSignature_2346_);
v_value_2347_ = lean_ctor_get(v_decl_2340_, 1);
lean_inc_ref(v_value_2347_);
lean_dec_ref(v_decl_2340_);
v_name_2348_ = lean_ctor_get(v_toSignature_2346_, 0);
lean_inc(v_name_2348_);
v_type_2349_ = lean_ctor_get(v_toSignature_2346_, 2);
lean_inc_ref(v_type_2349_);
v_params_2350_ = lean_ctor_get(v_toSignature_2346_, 3);
lean_inc_ref(v_params_2350_);
lean_dec_ref(v_toSignature_2346_);
v___x_2351_ = lean_box(v_pu_2339_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2352_, 0, v___x_2351_);
lean_closure_set(v___f_2352_, 1, v_params_2350_);
lean_closure_set(v___f_2352_, 2, v_type_2349_);
lean_closure_set(v___f_2352_, 3, v_value_2347_);
lean_closure_set(v___f_2352_, 4, v_name_2348_);
v___x_2353_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2352_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2354_, lean_object* v_decl_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
uint8_t v_pu_boxed_2361_; lean_object* v_res_2362_; 
v_pu_boxed_2361_ = lean_unbox(v_pu_2354_);
v_res_2362_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2361_, v_decl_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2363_, lean_object* v_decl_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2363_, v_decl_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2381_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2376_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v_a_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2377_);
v___x_2379_ = v___x_2374_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2382_, lean_object* v_decl_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_pu_boxed_2390_; lean_object* v_res_2391_; 
v_pu_boxed_2390_ = lean_unbox(v_pu_2382_);
v_res_2391_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2390_, v_decl_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2392_, lean_object* v_decl_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_box(v_pu_2392_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2400_, 0, v___x_2399_);
lean_closure_set(v___f_2400_, 1, v_decl_2393_);
v___x_2401_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2400_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2402_, lean_object* v_decl_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v_pu_boxed_2409_; lean_object* v_res_2410_; 
v_pu_boxed_2409_ = lean_unbox(v_pu_2402_);
v_res_2410_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2409_, v_decl_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2411_, lean_object* v_val_2412_, lean_object* v_a_x3f_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_st_ref_swap(v_a_2411_, v_val_2412_);
lean_dec(v___x_2416_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2418_, lean_object* v_val_2419_, lean_object* v_a_x3f_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2418_, v_val_2419_, v_a_x3f_2420_);
lean_dec(v_a_x3f_2420_);
lean_dec(v_a_2418_);
return v_res_2422_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_unsigned_to_nat(16u);
v___x_2425_ = lean_mk_array(v___x_2424_, v___x_2423_);
return v___x_2425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2426_);
return v___x_2428_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2430_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
lean_ctor_set(v___x_2430_, 2, v___x_2429_);
lean_ctor_set(v___x_2430_, 3, v___x_2429_);
lean_ctor_set(v___x_2430_, 4, v___x_2429_);
lean_ctor_set(v___x_2430_, 5, v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_unsigned_to_nat(1u);
v___x_2432_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2434_, lean_object* v_x_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_r_2441_; 
v___x_2439_ = lean_st_ref_get(v_a_2437_);
v___x_2440_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2441_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2435_, v___x_2440_, v_phase_2434_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v_r_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2458_; 
v_a_2442_ = lean_ctor_get(v_r_2441_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_r_2441_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2444_ = v_r_2441_;
v_isShared_2445_ = v_isSharedCheck_2458_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v_r_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2458_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
lean_inc(v_a_2442_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 1);
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v___x_2448_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2437_, v___x_2439_, v___x_2447_);
lean_dec_ref(v___x_2447_);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2448_, 0);
lean_dec(v_unused_2456_);
v___x_2450_ = v___x_2448_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v___x_2448_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_a_2442_);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2442_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_a_2459_ = lean_ctor_get(v_r_2441_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v_r_2441_, 1);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2437_, v___x_2439_, v___x_2460_);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2461_, 0);
lean_dec(v_unused_2469_);
v___x_2463_ = v___x_2461_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v___x_2461_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
lean_ctor_set(v___x_2463_, 0, v_a_2459_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2459_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2470_, lean_object* v_x_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
uint8_t v_phase_boxed_2475_; lean_object* v_res_2476_; 
v_phase_boxed_2475_ = lean_unbox(v_phase_2470_);
v_res_2476_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2475_, v_x_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2477_, uint8_t v_phase_2478_, lean_object* v_x_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2478_, v_x_2479_, v_a_2480_, v_a_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2484_, lean_object* v_phase_2485_, lean_object* v_x_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
uint8_t v_phase_boxed_2490_; lean_object* v_res_2491_; 
v_phase_boxed_2490_ = lean_unbox(v_phase_2485_);
v_res_2491_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2484_, v_phase_boxed_2490_, v_x_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2492_, lean_object* v_decl_2493_, lean_object* v___x_2494_, uint8_t v___x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2492_, v_decl_2493_, v___x_2494_, v___x_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2492_, v_a_2502_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
return v___x_2503_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_a_2504_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2501_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2501_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2512_, lean_object* v_decl_2513_, lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v_pu_boxed_2521_; uint8_t v___x_100__boxed_2522_; lean_object* v_res_2523_; 
v_pu_boxed_2521_ = lean_unbox(v_pu_2512_);
v___x_100__boxed_2522_ = lean_unbox(v___x_2515_);
v_res_2523_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2521_, v_decl_2513_, v___x_2514_, v___x_100__boxed_2522_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2524_, lean_object* v_decl_2525_, uint8_t v_phase_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; 
v___x_2530_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2531_ = 0;
v___x_2532_ = lean_box(v_pu_2524_);
v___x_2533_ = lean_box(v___x_2531_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2534_, 0, v___x_2532_);
lean_closure_set(v___f_2534_, 1, v_decl_2525_);
lean_closure_set(v___f_2534_, 2, v___x_2530_);
lean_closure_set(v___f_2534_, 3, v___x_2533_);
v___x_2535_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2526_, v___f_2534_, v_a_2527_, v_a_2528_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2536_, lean_object* v_decl_2537_, lean_object* v_phase_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
uint8_t v_pu_boxed_2542_; uint8_t v_phase_boxed_2543_; lean_object* v_res_2544_; 
v_pu_boxed_2542_ = lean_unbox(v_pu_2536_);
v_phase_boxed_2543_ = lean_unbox(v_phase_2538_);
v_res_2544_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2542_, v_decl_2537_, v_phase_boxed_2543_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2545_, lean_object* v_code_2546_, lean_object* v___x_2547_, uint8_t v___x_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2545_, v_code_2546_, v___x_2547_, v___x_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2545_, v_a_2555_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2556_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_a_2557_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2554_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2554_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2565_, lean_object* v_code_2566_, lean_object* v___x_2567_, lean_object* v___x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
uint8_t v_pu_boxed_2574_; uint8_t v___x_100__boxed_2575_; lean_object* v_res_2576_; 
v_pu_boxed_2574_ = lean_unbox(v_pu_2565_);
v___x_100__boxed_2575_ = lean_unbox(v___x_2568_);
v_res_2576_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2574_, v_code_2566_, v___x_2567_, v___x_100__boxed_2575_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2577_, lean_object* v_code_2578_, uint8_t v_phase_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; 
v___x_2583_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2584_ = 0;
v___x_2585_ = lean_box(v_pu_2577_);
v___x_2586_ = lean_box(v___x_2584_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2587_, 0, v___x_2585_);
lean_closure_set(v___f_2587_, 1, v_code_2578_);
lean_closure_set(v___f_2587_, 2, v___x_2583_);
lean_closure_set(v___f_2587_, 3, v___x_2586_);
v___x_2588_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2579_, v___f_2587_, v_a_2580_, v_a_2581_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2589_, lean_object* v_code_2590_, lean_object* v_phase_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
uint8_t v_pu_boxed_2595_; uint8_t v_phase_boxed_2596_; lean_object* v_res_2597_; 
v_pu_boxed_2595_ = lean_unbox(v_pu_2589_);
v_phase_boxed_2596_ = lean_unbox(v_phase_2591_);
v_res_2597_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2595_, v_code_2590_, v_phase_boxed_2596_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
return v_res_2597_;
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

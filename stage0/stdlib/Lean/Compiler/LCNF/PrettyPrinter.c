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
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object* v_f_6_, lean_object* v_a_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6_ = stack[0].m_obj;
lean_object* v_a_7_ = stack[1].m_obj;
lean_object* v_b_8_ = stack[2].m_obj;
lean_object* v___y_9_ = stack[3].m_obj;
lean_object* v___y_10_ = stack[4].m_obj;
lean_object* v___y_11_ = stack[5].m_obj;
lean_object* v___y_12_ = stack[6].m_obj;
lean_object* v___y_13_ = stack[7].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_6_, v_a_7_, v_b_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object* v_f_37_, lean_object* v_a_38_, lean_object* v_b_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_37_, v_a_38_, v_b_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_46_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object* v_as_47_, lean_object* v_f_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_array_get_size(v_as_47_);
v___x_57_ = lean_nat_dec_lt(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec_ref(v_f_48_);
lean_dec_ref(v_as_47_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_array_fget_borrowed(v_as_47_, v___x_55_);
lean_inc_ref(v_f_48_);
lean_inc(v_a_53_);
lean_inc_ref(v_a_52_);
lean_inc(v_a_51_);
lean_inc_ref(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v___x_60_);
v___x_61_ = lean_apply_7(v_f_48_, v___x_60_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, lean_box(0));
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_61_, 1);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = l_Array_toSubarray___redArg(v_as_47_, v___x_63_, v___x_56_);
v___x_65_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_48_, v___x_64_, v_a_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
return v___x_65_;
}
else
{
lean_dec_ref(v_f_48_);
lean_dec_ref(v_as_47_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_47_ = stack[0].m_obj;
lean_object* v_f_48_ = stack[1].m_obj;
lean_object* v_a_49_ = stack[2].m_obj;
lean_object* v_a_50_ = stack[3].m_obj;
lean_object* v_a_51_ = stack[4].m_obj;
lean_object* v_a_52_ = stack[5].m_obj;
lean_object* v_a_53_ = stack[6].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(v_as_47_, v_f_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(lean_object* v_as_67_, lean_object* v_f_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(v_as_67_, v_f_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_75_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object* v_00_u03b1_76_, lean_object* v_as_77_, lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(v_as_77_, v_f_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
return v___x_85_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_77_ = stack[1].m_obj;
lean_object* v_f_78_ = stack[2].m_obj;
lean_object* v_a_79_ = stack[3].m_obj;
lean_object* v_a_80_ = stack[4].m_obj;
lean_object* v_a_81_ = stack[5].m_obj;
lean_object* v_a_82_ = stack[6].m_obj;
lean_object* v_a_83_ = stack[7].m_obj;
lean_object* v_res_86_;
v_res_86_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_box(0), v_as_77_, v_f_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(lean_object* v_00_u03b1_87_, lean_object* v_as_88_, lean_object* v_f_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(v_00_u03b1_87_, v_as_88_, v_f_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_96_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object* v_00_u03b1_97_, lean_object* v_f_98_, lean_object* v_inst_99_, lean_object* v_R_100_, lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_c_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_98_, v_a_101_, v_b_102_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
return v___x_110_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_98_ = stack[1].m_obj;
lean_object* v_a_101_ = stack[4].m_obj;
lean_object* v_b_102_ = stack[5].m_obj;
lean_object* v___y_104_ = stack[7].m_obj;
lean_object* v___y_105_ = stack[8].m_obj;
lean_object* v___y_106_ = stack[9].m_obj;
lean_object* v___y_107_ = stack[10].m_obj;
lean_object* v___y_108_ = stack[11].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_box(0), v_f_98_, lean_box(0), lean_box(0), v_a_101_, v_b_102_, lean_box(0), v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object* v_00_u03b1_112_, lean_object* v_f_113_, lean_object* v_inst_114_, lean_object* v_R_115_, lean_object* v_a_116_, lean_object* v_b_117_, lean_object* v_c_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(v_00_u03b1_112_, v_f_113_, v_inst_114_, v_R_115_, v_a_116_, v_b_117_, v_c_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_125_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object* v_f_126_, lean_object* v_pre_127_, lean_object* v_as_128_, size_t v_sz_129_, size_t v_i_130_, lean_object* v_b_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_lt(v_i_130_, v_sz_129_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_dec(v_pre_127_);
lean_dec_ref(v_f_126_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_b_131_);
return v___x_139_;
}
else
{
lean_object* v_a_140_; lean_object* v___x_141_; 
v_a_140_ = lean_array_uget_borrowed(v_as_128_, v_i_130_);
lean_inc_ref(v_f_126_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc_ref(v___y_132_);
lean_inc(v_a_140_);
v___x_141_ = lean_apply_7(v_f_126_, v_a_140_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; size_t v___x_145_; size_t v___x_146_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_141_, 1);
lean_inc(v_pre_127_);
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v_b_131_);
lean_ctor_set(v___x_143_, 1, v_pre_127_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_142_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_130_, v___x_145_);
v_i_130_ = v___x_146_;
v_b_131_ = v___x_144_;
goto _start;
}
else
{
lean_dec(v_b_131_);
lean_dec(v_pre_127_);
lean_dec_ref(v_f_126_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_126_ = stack[0].m_obj;
lean_object* v_pre_127_ = stack[1].m_obj;
lean_object* v_as_128_ = stack[2].m_obj;
size_t v_sz_129_ = stack[3].m_num;
size_t v_i_130_ = stack[4].m_num;
lean_object* v_b_131_ = stack[5].m_obj;
lean_object* v___y_132_ = stack[6].m_obj;
lean_object* v___y_133_ = stack[7].m_obj;
lean_object* v___y_134_ = stack[8].m_obj;
lean_object* v___y_135_ = stack[9].m_obj;
lean_object* v___y_136_ = stack[10].m_obj;
lean_object* v_res_148_;
v_res_148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_126_, v_pre_127_, v_as_128_, v_sz_129_, v_i_130_, v_b_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object* v_f_149_, lean_object* v_pre_150_, lean_object* v_as_151_, lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
size_t v_sz_boxed_161_; size_t v_i_boxed_162_; lean_object* v_res_163_; 
v_sz_boxed_161_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_162_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_149_, v_pre_150_, v_as_151_, v_sz_boxed_161_, v_i_boxed_162_, v_b_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec_ref(v_as_151_);
return v_res_163_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object* v_pre_164_, lean_object* v_as_165_, lean_object* v_f_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_result_173_; size_t v_sz_174_; size_t v___x_175_; lean_object* v___x_176_; 
v_result_173_ = lean_box(0);
v_sz_174_ = lean_array_size(v_as_165_);
v___x_175_ = ((size_t)0ULL);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_166_, v_pre_164_, v_as_165_, v_sz_174_, v___x_175_, v_result_173_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_176_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_164_ = stack[0].m_obj;
lean_object* v_as_165_ = stack[1].m_obj;
lean_object* v_f_166_ = stack[2].m_obj;
lean_object* v_a_167_ = stack[3].m_obj;
lean_object* v_a_168_ = stack[4].m_obj;
lean_object* v_a_169_ = stack[5].m_obj;
lean_object* v_a_170_ = stack[6].m_obj;
lean_object* v_a_171_ = stack[7].m_obj;
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v_pre_164_, v_as_165_, v_f_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object* v_pre_178_, lean_object* v_as_179_, lean_object* v_f_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v_pre_178_, v_as_179_, v_f_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec_ref(v_as_179_);
return v_res_187_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object* v_00_u03b1_188_, lean_object* v_pre_189_, lean_object* v_as_190_, lean_object* v_f_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v_pre_189_, v_as_190_, v_f_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
return v___x_198_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_189_ = stack[1].m_obj;
lean_object* v_as_190_ = stack[2].m_obj;
lean_object* v_f_191_ = stack[3].m_obj;
lean_object* v_a_192_ = stack[4].m_obj;
lean_object* v_a_193_ = stack[5].m_obj;
lean_object* v_a_194_ = stack[6].m_obj;
lean_object* v_a_195_ = stack[7].m_obj;
lean_object* v_a_196_ = stack[8].m_obj;
lean_object* v_res_199_;
v_res_199_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_box(0), v_pre_189_, v_as_190_, v_f_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object* v_00_u03b1_200_, lean_object* v_pre_201_, lean_object* v_as_202_, lean_object* v_f_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(v_00_u03b1_200_, v_pre_201_, v_as_202_, v_f_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_as_202_);
return v_res_210_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object* v_00_u03b1_211_, lean_object* v_f_212_, lean_object* v_pre_213_, lean_object* v_as_214_, size_t v_sz_215_, size_t v_i_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_212_, v_pre_213_, v_as_214_, v_sz_215_, v_i_216_, v_b_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
return v___x_224_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_212_ = stack[1].m_obj;
lean_object* v_pre_213_ = stack[2].m_obj;
lean_object* v_as_214_ = stack[3].m_obj;
size_t v_sz_215_ = stack[4].m_num;
size_t v_i_216_ = stack[5].m_num;
lean_object* v_b_217_ = stack[6].m_obj;
lean_object* v___y_218_ = stack[7].m_obj;
lean_object* v___y_219_ = stack[8].m_obj;
lean_object* v___y_220_ = stack[9].m_obj;
lean_object* v___y_221_ = stack[10].m_obj;
lean_object* v___y_222_ = stack[11].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_box(0), v_f_212_, v_pre_213_, v_as_214_, v_sz_215_, v_i_216_, v_b_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object* v_00_u03b1_226_, lean_object* v_f_227_, lean_object* v_pre_228_, lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_b_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
size_t v_sz_boxed_239_; size_t v_i_boxed_240_; lean_object* v_res_241_; 
v_sz_boxed_239_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_240_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(v_00_u03b1_226_, v_f_227_, v_pre_228_, v_as_229_, v_sz_boxed_239_, v_i_boxed_240_, v_b_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec_ref(v_as_229_);
return v_res_241_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object* v_fvarId_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_248_; 
lean_inc(v_fvarId_242_);
v___x_248_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_fvarId_242_);
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_259_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_253_ = 1;
v___x_254_ = l_Lean_Name_toString(v_a_249_, v___x_253_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_255_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_277_; 
v_a_260_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_262_ = v___x_248_;
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_248_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
uint8_t v___y_265_; uint8_t v___x_275_; 
v___x_275_ = l_Lean_Exception_isInterrupt(v_a_260_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
lean_inc(v_a_260_);
v___x_276_ = l_Lean_Exception_isRuntime(v_a_260_);
v___y_265_ = v___x_276_;
goto v___jp_264_;
}
else
{
v___y_265_ = v___x_275_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
lean_dec(v_a_260_);
v___x_266_ = 1;
v___x_267_ = l_Lean_Name_toString(v_fvarId_242_, v___x_266_);
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 0);
lean_ctor_set(v___x_262_, 0, v___x_268_);
v___x_270_ = v___x_262_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
else
{
lean_object* v___x_273_; 
lean_dec(v_fvarId_242_);
if (v_isShared_263_ == 0)
{
v___x_273_ = v___x_262_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_260_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_242_ = stack[0].m_obj;
lean_object* v_a_243_ = stack[1].m_obj;
lean_object* v_a_244_ = stack[2].m_obj;
lean_object* v_a_245_ = stack[3].m_obj;
lean_object* v_a_246_ = stack[4].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object* v_fvarId_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_285_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* v_fvarId_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_286_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_286_ = stack[0].m_obj;
lean_object* v_a_287_ = stack[1].m_obj;
lean_object* v_a_288_ = stack[2].m_obj;
lean_object* v_a_289_ = stack[3].m_obj;
lean_object* v_a_290_ = stack[4].m_obj;
lean_object* v_a_291_ = stack[5].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Compiler_LCNF_PP_ppFVar(v_fvarId_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* v_fvarId_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Compiler_LCNF_PP_ppFVar(v_fvarId_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_302_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_309_; uint64_t v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2(void){
_start:
{
uint64_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_uint64_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1);
v___x_312_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_313_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint64(v___x_313_, sizeof(void*)*1, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_320_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
lean_ctor_set(v___x_322_, 3, v___x_321_);
lean_ctor_set(v___x_322_, 4, v___x_320_);
lean_ctor_set(v___x_322_, 5, v___x_320_);
lean_ctor_set(v___x_322_, 6, v___x_320_);
lean_ctor_set(v___x_322_, 7, v___x_320_);
lean_ctor_set(v___x_322_, 8, v___x_320_);
lean_ctor_set(v___x_322_, 9, v___x_320_);
lean_ctor_set(v___x_322_, 10, v___x_320_);
lean_ctor_set(v___x_322_, 11, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_324_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v___x_323_);
lean_ctor_set(v___x_324_, 3, v___x_323_);
lean_ctor_set(v___x_324_, 4, v___x_323_);
lean_ctor_set(v___x_324_, 5, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_unsigned_to_nat(32u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9(void){
_start:
{
size_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_328_ = ((size_t)5ULL);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_unsigned_to_nat(32u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
v___x_333_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
lean_ctor_set(v___x_333_, 2, v___x_329_);
lean_ctor_set(v___x_333_, 3, v___x_329_);
lean_ctor_set_usize(v___x_333_, 4, v___x_328_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
lean_ctor_set(v___x_335_, 4, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_336_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10);
v___x_337_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
v___x_338_ = lean_box(1);
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
v___x_340_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
v___x_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___x_338_);
lean_ctor_set(v___x_341_, 3, v___x_337_);
lean_ctor_set(v___x_341_, 4, v___x_336_);
return v___x_341_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_347_ = lean_box(1);
v___x_348_ = 0;
v___x_349_ = 1;
v___x_350_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3));
v___x_353_ = lean_box(0);
lean_inc_ref(v_a_343_);
v___x_354_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_354_, 0, v___x_350_);
lean_ctor_set(v___x_354_, 1, v___x_347_);
lean_ctor_set(v___x_354_, 2, v_a_343_);
lean_ctor_set(v___x_354_, 3, v___x_352_);
lean_ctor_set(v___x_354_, 4, v___x_353_);
lean_ctor_set(v___x_354_, 5, v___x_351_);
lean_ctor_set(v___x_354_, 6, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*7, v___x_348_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*7 + 1, v___x_348_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*7 + 2, v___x_348_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*7 + 3, v___x_349_);
v___x_355_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11);
v___x_356_ = lean_st_mk_ref(v___x_355_);
v___x_357_ = l_Lean_Meta_ppExpr(v_e_342_, v___x_354_, v___x_356_, v_a_344_, v_a_345_);
lean_dec_ref_known(v___x_354_, 7);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_st_ref_get(v___x_356_);
lean_dec(v___x_356_);
lean_dec(v___x_362_);
if (v_isShared_361_ == 0)
{
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_358_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_dec(v___x_356_);
return v___x_357_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_342_ = stack[0].m_obj;
lean_object* v_a_343_ = stack[1].m_obj;
lean_object* v_a_344_ = stack[2].m_obj;
lean_object* v_a_345_ = stack[3].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_342_, v_a_343_, v_a_344_, v_a_345_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_373_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_374_, v_a_375_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_374_ = stack[0].m_obj;
lean_object* v_a_375_ = stack[1].m_obj;
lean_object* v_a_376_ = stack[2].m_obj;
lean_object* v_a_377_ = stack[3].m_obj;
lean_object* v_a_378_ = stack[4].m_obj;
lean_object* v_a_379_ = stack[5].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_390_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* v_opts_391_, lean_object* v_opt_392_){
_start:
{
lean_object* v_name_393_; lean_object* v_defValue_394_; lean_object* v_map_395_; lean_object* v___x_396_; 
v_name_393_ = lean_ctor_get(v_opt_392_, 0);
v_defValue_394_ = lean_ctor_get(v_opt_392_, 1);
v_map_395_ = lean_ctor_get(v_opts_391_, 0);
v___x_396_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_395_, v_name_393_);
if (lean_obj_tag(v___x_396_) == 0)
{
uint8_t v___x_397_; 
v___x_397_ = lean_unbox(v_defValue_394_);
return v___x_397_;
}
else
{
lean_object* v_val_398_; 
v_val_398_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v___x_396_, 1);
if (lean_obj_tag(v_val_398_) == 1)
{
uint8_t v_v_399_; 
v_v_399_ = lean_ctor_get_uint8(v_val_398_, 0);
lean_dec_ref_known(v_val_398_, 0);
return v_v_399_;
}
else
{
uint8_t v___x_400_; 
lean_dec(v_val_398_);
v___x_400_ = lean_unbox(v_defValue_394_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_391_ = stack[0].m_obj;
lean_object* v_opt_392_ = stack[1].m_obj;
uint8_t v_res_401_;
v_res_401_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_391_, v_opt_392_);
stack->m_num = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* v_opts_402_, lean_object* v_opt_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_402_, v_opt_403_);
lean_dec_ref(v_opt_403_);
lean_dec_ref(v_opts_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_nat_to_int(v_a_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
v___x_417_ = lean_string_length(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
v___x_419_ = lean_nat_to_int(v___x_418_);
return v___x_419_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
switch(lean_obj_tag(v_e_424_))
{
case 0:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
case 1:
{
lean_object* v_fvarId_433_; lean_object* v___x_434_; 
v_fvarId_433_ = lean_ctor_get(v_e_424_, 0);
lean_inc(v_fvarId_433_);
lean_dec_ref_known(v_e_424_, 1);
v___x_434_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_433_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v___x_434_;
}
default: 
{
lean_object* v_expr_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_471_; 
v_expr_435_ = lean_ctor_get(v_e_424_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_e_424_);
if (v_isSharedCheck_471_ == 0)
{
v___x_437_ = v_e_424_;
v_isShared_438_ = v_isSharedCheck_471_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_expr_435_);
lean_dec(v_e_424_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_471_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_428_);
v___x_440_ = l_Lean_pp_explicit;
v___x_441_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_439_, v___x_440_);
lean_dec_ref(v___x_439_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec_ref(v_expr_435_);
v___x_442_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 0);
lean_ctor_set(v___x_437_, 0, v___x_442_);
v___x_444_ = v___x_437_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
uint8_t v___x_446_; 
lean_del_object(v___x_437_);
v___x_446_ = l_Lean_Expr_isConst(v_expr_435_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_Expr_isProp(v_expr_435_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_Expr_isType0(v_expr_435_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_Expr_isFVar(v_expr_435_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_435_, v_a_425_, v_a_428_, v_a_429_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_466_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_466_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_466_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_466_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_455_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_456_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_a_451_);
v___x_458_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_455_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = 0;
v___x_462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_461_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_462_);
v___x_464_ = v___x_453_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
return v___x_450_;
}
}
else
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_435_, v_a_425_, v_a_428_, v_a_429_);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_435_, v_a_425_, v_a_428_, v_a_429_);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_435_, v_a_425_, v_a_428_, v_a_429_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_435_, v_a_425_, v_a_428_, v_a_429_);
return v___x_470_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_424_ = stack[0].m_obj;
lean_object* v_a_425_ = stack[1].m_obj;
lean_object* v_a_426_ = stack[2].m_obj;
lean_object* v_a_427_ = stack[3].m_obj;
lean_object* v_a_428_ = stack[4].m_obj;
lean_object* v_a_429_ = stack[5].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_480_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t v_pu_481_, lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_481_ = stack[0].m_num;
lean_object* v_e_482_ = stack[1].m_obj;
lean_object* v_a_483_ = stack[2].m_obj;
lean_object* v_a_484_ = stack[3].m_obj;
lean_object* v_a_485_ = stack[4].m_obj;
lean_object* v_a_486_ = stack[5].m_obj;
lean_object* v_a_487_ = stack[6].m_obj;
lean_object* v_res_490_;
v_res_490_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_481_, v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* v_pu_491_, lean_object* v_e_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
uint8_t v_pu_boxed_499_; lean_object* v_res_500_; 
v_pu_boxed_499_ = lean_unbox(v_pu_491_);
v_res_500_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_boxed_499_, v_e_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_500_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t v_pu_501_, lean_object* v_args_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_509_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_510_ = lean_box(v_pu_501_);
v___x_511_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(v___x_511_, 0, v___x_510_);
v___x_512_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_509_, v_args_502_, v___x_511_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_512_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_501_ = stack[0].m_num;
lean_object* v_args_502_ = stack[1].m_obj;
lean_object* v_a_503_ = stack[2].m_obj;
lean_object* v_a_504_ = stack[3].m_obj;
lean_object* v_a_505_ = stack[4].m_obj;
lean_object* v_a_506_ = stack[5].m_obj;
lean_object* v_a_507_ = stack[6].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_501_, v_args_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* v_pu_514_, lean_object* v_args_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
uint8_t v_pu_boxed_522_; lean_object* v_res_523_; 
v_pu_boxed_522_ = lean_unbox(v_pu_514_);
v_res_523_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_boxed_522_, v_args_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_args_515_);
return v_res_523_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* v_lit_524_){
_start:
{
uint64_t v_v_527_; 
switch(lean_obj_tag(v_lit_524_))
{
case 0:
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v_val_532_ = lean_ctor_get(v_lit_524_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_lit_524_);
if (v_isSharedCheck_541_ == 0)
{
v___x_534_ = v_lit_524_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v_lit_524_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = l_Nat_reprFast(v_val_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 3);
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
case 1:
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v_val_542_ = lean_ctor_get(v_lit_524_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_lit_524_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v_lit_524_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v_lit_524_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = l_String_quote(v_val_542_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 3);
lean_ctor_set(v___x_544_, 0, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
case 2:
{
uint8_t v_val_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_val_552_ = lean_ctor_get_uint8(v_lit_524_, 0);
lean_dec_ref_known(v_lit_524_, 0);
v___x_553_ = lean_uint8_to_nat(v_val_552_);
v___x_554_ = l_Nat_reprFast(v___x_553_);
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
case 3:
{
uint16_t v_val_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_val_557_ = lean_ctor_get_uint16(v_lit_524_, 0);
lean_dec_ref_known(v_lit_524_, 0);
v___x_558_ = lean_uint16_to_nat(v_val_557_);
v___x_559_ = l_Nat_reprFast(v___x_558_);
v___x_560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
case 4:
{
uint32_t v_val_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_val_562_ = lean_ctor_get_uint32(v_lit_524_, 0);
lean_dec_ref_known(v_lit_524_, 0);
v___x_563_ = lean_uint32_to_nat(v_val_562_);
v___x_564_ = l_Nat_reprFast(v___x_563_);
v___x_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
default: 
{
uint64_t v_val_567_; 
v_val_567_ = lean_ctor_get_uint64(v_lit_524_, 0);
lean_dec_ref(v_lit_524_);
v_v_527_ = v_val_567_;
goto v___jp_526_;
}
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_uint64_to_nat(v_v_527_);
v___x_529_ = l_Nat_reprFast(v___x_528_);
v___x_530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppLitValue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lit_524_ = stack[0].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_524_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* v_lit_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_569_);
return v_res_571_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* v_lit_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_572_);
return v___x_579_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppLitValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_lit_572_ = stack[0].m_obj;
lean_object* v_a_573_ = stack[1].m_obj;
lean_object* v_a_574_ = stack[2].m_obj;
lean_object* v_a_575_ = stack[3].m_obj;
lean_object* v_a_576_ = stack[4].m_obj;
lean_object* v_a_577_ = stack[5].m_obj;
lean_object* v_res_580_;
v_res_580_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* v_lit_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* v_x_601_){
_start:
{
lean_object* v_name_602_; lean_object* v_cidx_603_; lean_object* v_usize_604_; lean_object* v_ssize_605_; lean_object* v_r_607_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_r_621_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_name_602_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_name_602_);
v_cidx_603_ = lean_ctor_get(v_x_601_, 1);
lean_inc(v_cidx_603_);
v_usize_604_ = lean_ctor_get(v_x_601_, 3);
lean_inc(v_usize_604_);
v_ssize_605_ = lean_ctor_get(v_x_601_, 4);
lean_inc(v_ssize_605_);
lean_dec_ref(v_x_601_);
v___x_618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
v___x_619_ = l_Nat_reprFast(v_cidx_603_);
v___x_620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v_r_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_621_, 0, v___x_618_);
lean_ctor_set(v_r_621_, 1, v___x_620_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_lt(v___x_632_, v_usize_604_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v___x_632_, v_ssize_605_);
if (v___x_634_ == 0)
{
lean_dec(v_ssize_605_);
lean_dec(v_usize_604_);
v_r_607_ = v_r_621_;
goto v___jp_606_;
}
else
{
goto v___jp_622_;
}
}
else
{
goto v___jp_622_;
}
v___jp_606_:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = lean_name_eq(v_name_602_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_r_617_; 
v___x_610_ = 1;
v___x_611_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v_r_607_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_Name_toString(v_name_602_, v___x_610_);
v___x_614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_612_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v_r_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_617_, 0, v___x_615_);
lean_ctor_set(v_r_617_, 1, v___x_616_);
return v_r_617_;
}
else
{
lean_dec(v_name_602_);
return v_r_607_;
}
}
v___jp_622_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_r_631_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v_r_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Nat_reprFast(v_usize_604_);
v___x_626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_624_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_623_);
v___x_629_ = l_Nat_reprFast(v_ssize_605_);
v___x_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v_r_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_631_, 0, v___x_628_);
lean_ctor_set(v_r_631_, 1, v___x_630_);
v_r_607_ = v_r_631_;
goto v___jp_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_635_);
return v___x_636_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
switch(lean_obj_tag(v_e_685_))
{
case 0:
{
lean_object* v_value_692_; lean_object* v___x_693_; 
v_value_692_ = lean_ctor_get(v_e_685_, 0);
lean_inc_ref(v_value_692_);
lean_dec_ref_known(v_e_685_, 1);
v___x_693_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_692_);
return v___x_693_;
}
case 1:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
case 2:
{
lean_object* v_idx_696_; lean_object* v_struct_697_; lean_object* v___x_698_; 
v_idx_696_ = lean_ctor_get(v_e_685_, 1);
lean_inc(v_idx_696_);
v_struct_697_ = lean_ctor_get(v_e_685_, 2);
lean_inc(v_struct_697_);
lean_dec_ref_known(v_e_685_, 3);
v___x_698_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_697_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_711_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_711_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_711_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_711_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_703_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v_a_699_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Nat_reprFast(v_idx_696_);
v___x_706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_707_);
v___x_709_ = v___x_701_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_dec(v_idx_696_);
return v___x_698_;
}
}
case 3:
{
lean_object* v_declName_712_; lean_object* v_us_713_; lean_object* v_args_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_declName_712_ = lean_ctor_get(v_e_685_, 0);
lean_inc(v_declName_712_);
v_us_713_ = lean_ctor_get(v_e_685_, 1);
lean_inc(v_us_713_);
v_args_714_ = lean_ctor_get(v_e_685_, 2);
lean_inc_ref(v_args_714_);
lean_dec_ref_known(v_e_685_, 3);
v___x_715_ = l_Lean_Expr_const___override(v_declName_712_, v_us_713_);
v___x_716_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_715_, v_a_686_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_714_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_714_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v_a_717_);
lean_ctor_set(v___x_723_, 1, v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_dec(v_a_717_);
return v___x_718_;
}
}
else
{
lean_dec_ref(v_args_714_);
return v___x_716_;
}
}
case 4:
{
lean_object* v_fvarId_728_; lean_object* v_args_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_747_; 
v_fvarId_728_ = lean_ctor_get(v_e_685_, 0);
v_args_729_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_747_ == 0)
{
v___x_731_ = v_e_685_;
v_isShared_732_ = v_isSharedCheck_747_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_args_729_);
lean_inc(v_fvarId_728_);
lean_dec(v_e_685_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_747_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_728_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_729_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_729_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_746_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 5);
lean_ctor_set(v___x_731_, 1, v_a_736_);
lean_ctor_set(v___x_731_, 0, v_a_734_);
v___x_741_ = v___x_731_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_734_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_736_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
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
lean_dec(v_a_734_);
lean_del_object(v___x_731_);
return v___x_735_;
}
}
else
{
lean_del_object(v___x_731_);
lean_dec_ref(v_args_729_);
return v___x_733_;
}
}
}
case 5:
{
lean_object* v_i_748_; lean_object* v_args_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_766_; 
v_i_748_ = lean_ctor_get(v_e_685_, 0);
v_args_749_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_766_ == 0)
{
v___x_751_ = v_e_685_;
v_isShared_752_ = v_isSharedCheck_766_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_args_749_);
lean_inc(v_i_748_);
lean_dec(v_e_685_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_766_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_749_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_765_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_765_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_748_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_a_754_);
lean_ctor_set(v___x_751_, 0, v___x_758_);
v___x_760_ = v___x_751_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_754_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_760_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_del_object(v___x_751_);
lean_dec_ref(v_i_748_);
return v___x_753_;
}
}
}
case 6:
{
lean_object* v_i_767_; lean_object* v_var_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_790_; 
v_i_767_ = lean_ctor_get(v_e_685_, 0);
v_var_768_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_790_ == 0)
{
v___x_770_ = v_e_685_;
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_var_768_);
lean_inc(v_i_767_);
lean_dec(v_e_685_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_768_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_789_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_789_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_789_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_789_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_777_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_778_ = l_Nat_reprFast(v_i_767_);
v___x_779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 5);
lean_ctor_set(v___x_770_, 1, v___x_779_);
lean_ctor_set(v___x_770_, 0, v___x_777_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_788_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_a_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_784_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_del_object(v___x_770_);
lean_dec(v_i_767_);
return v___x_772_;
}
}
}
case 7:
{
lean_object* v_i_791_; lean_object* v_var_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_814_; 
v_i_791_ = lean_ctor_get(v_e_685_, 0);
v_var_792_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_814_ == 0)
{
v___x_794_ = v_e_685_;
v_isShared_795_ = v_isSharedCheck_814_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_var_792_);
lean_inc(v_i_791_);
lean_dec(v_e_685_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_814_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_792_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_813_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_813_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_801_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
v___x_802_ = l_Nat_reprFast(v_i_791_);
v___x_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 5);
lean_ctor_set(v___x_794_, 1, v___x_803_);
lean_ctor_set(v___x_794_, 0, v___x_801_);
v___x_805_ = v___x_794_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_812_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_806_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_a_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_808_);
v___x_810_ = v___x_799_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_del_object(v___x_794_);
lean_dec(v_i_791_);
return v___x_796_;
}
}
}
case 8:
{
lean_object* v_n_815_; lean_object* v_offset_816_; lean_object* v_var_817_; lean_object* v___x_818_; 
v_n_815_ = lean_ctor_get(v_e_685_, 0);
lean_inc(v_n_815_);
v_offset_816_ = lean_ctor_get(v_e_685_, 1);
lean_inc(v_offset_816_);
v_var_817_ = lean_ctor_get(v_e_685_, 2);
lean_inc(v_var_817_);
lean_dec_ref_known(v_e_685_, 3);
v___x_818_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_817_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_838_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_838_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_823_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_824_ = l_Nat_reprFast(v_n_815_);
v___x_825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Nat_reprFast(v_offset_816_);
v___x_830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_834_);
v___x_836_ = v___x_821_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_dec(v_offset_816_);
lean_dec(v_n_815_);
return v___x_818_;
}
}
case 9:
{
lean_object* v_fn_839_; lean_object* v_args_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_859_; 
v_fn_839_ = lean_ctor_get(v_e_685_, 0);
v_args_840_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_859_ == 0)
{
v___x_842_ = v_e_685_;
v_isShared_843_ = v_isSharedCheck_859_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_args_840_);
lean_inc(v_fn_839_);
lean_dec(v_e_685_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_859_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_840_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_858_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_858_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_849_ = 1;
v___x_850_ = l_Lean_Name_toString(v_fn_839_, v___x_849_);
v___x_851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 5);
lean_ctor_set(v___x_842_, 1, v_a_845_);
lean_ctor_set(v___x_842_, 0, v___x_851_);
v___x_853_ = v___x_842_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_845_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_853_);
v___x_855_ = v___x_847_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_del_object(v___x_842_);
lean_dec(v_fn_839_);
return v___x_844_;
}
}
}
case 10:
{
lean_object* v_fn_860_; lean_object* v_args_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_882_; 
v_fn_860_ = lean_ctor_get(v_e_685_, 0);
v_args_861_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_882_ == 0)
{
v___x_863_ = v_e_685_;
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_args_861_);
lean_inc(v_fn_860_);
lean_dec(v_e_685_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_861_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_861_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_881_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_870_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_871_ = 1;
v___x_872_ = l_Lean_Name_toString(v_fn_860_, v___x_871_);
v___x_873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 5);
lean_ctor_set(v___x_863_, 1, v___x_873_);
lean_ctor_set(v___x_863_, 0, v___x_870_);
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_880_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_876_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
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
else
{
lean_del_object(v___x_863_);
lean_dec(v_fn_860_);
return v___x_865_;
}
}
}
case 11:
{
lean_object* v_n_883_; lean_object* v_var_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_906_; 
v_n_883_ = lean_ctor_get(v_e_685_, 0);
v_var_884_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_906_ == 0)
{
v___x_886_ = v_e_685_;
v_isShared_887_ = v_isSharedCheck_906_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_var_884_);
lean_inc(v_n_883_);
lean_dec(v_e_685_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_906_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_884_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_905_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_905_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_893_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_894_ = l_Nat_reprFast(v_n_883_);
v___x_895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 5);
lean_ctor_set(v___x_886_, 1, v___x_895_);
lean_ctor_set(v___x_886_, 0, v___x_893_);
v___x_897_ = v___x_886_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_898_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_900_);
v___x_902_ = v___x_891_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_del_object(v___x_886_);
lean_dec(v_n_883_);
return v___x_888_;
}
}
}
case 12:
{
lean_object* v_var_907_; lean_object* v_i_908_; uint8_t v_updateHeader_909_; lean_object* v_args_910_; lean_object* v___x_911_; 
v_var_907_ = lean_ctor_get(v_e_685_, 0);
lean_inc(v_var_907_);
v_i_908_ = lean_ctor_get(v_e_685_, 1);
lean_inc_ref(v_i_908_);
v_updateHeader_909_ = lean_ctor_get_uint8(v_e_685_, sizeof(void*)*3);
v_args_910_ = lean_ctor_get(v_e_685_, 2);
lean_inc_ref(v_args_910_);
lean_dec_ref_known(v_e_685_, 3);
v___x_911_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_907_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_684_, v_args_910_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_args_910_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_935_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_935_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___y_920_; 
v___x_918_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_909_ == 0)
{
lean_object* v___x_933_; 
v___x_933_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_920_ = v___x_933_;
goto v___jp_919_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_920_ = v___x_934_;
goto v___jp_919_;
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
lean_inc(v___y_920_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_918_);
lean_ctor_set(v___x_921_, 1, v___y_920_);
v___x_922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_a_912_);
v___x_924_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_908_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_a_914_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_921_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_929_);
v___x_931_ = v___x_916_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_dec(v_a_912_);
lean_dec_ref(v_i_908_);
return v___x_913_;
}
}
else
{
lean_dec_ref(v_args_910_);
lean_dec_ref(v_i_908_);
return v___x_911_;
}
}
case 13:
{
lean_object* v_fvarId_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_953_; 
v_fvarId_936_ = lean_ctor_get(v_e_685_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_e_685_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_e_685_, 0);
lean_dec(v_unused_954_);
v___x_938_ = v_e_685_;
v_isShared_939_ = v_isSharedCheck_953_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_fvarId_936_);
lean_dec(v_e_685_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_953_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_936_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_952_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_952_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 5);
lean_ctor_set(v___x_938_, 1, v_a_941_);
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_941_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_947_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_del_object(v___x_938_);
return v___x_940_;
}
}
}
case 14:
{
lean_object* v_fvarId_955_; lean_object* v___x_956_; 
v_fvarId_955_ = lean_ctor_get(v_e_685_, 0);
lean_inc(v_fvarId_955_);
lean_dec_ref_known(v_e_685_, 1);
v___x_956_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_955_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_966_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_966_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
return v___x_956_;
}
}
default: 
{
lean_object* v_fvarId_967_; lean_object* v___x_968_; 
v_fvarId_967_ = lean_ctor_get(v_e_685_, 0);
lean_inc(v_fvarId_967_);
lean_dec_ref_known(v_e_685_, 1);
v___x_968_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_967_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_684_ = stack[0].m_num;
lean_object* v_e_685_ = stack[1].m_obj;
lean_object* v_a_686_ = stack[2].m_obj;
lean_object* v_a_687_ = stack[3].m_obj;
lean_object* v_a_688_ = stack[4].m_obj;
lean_object* v_a_689_ = stack[5].m_obj;
lean_object* v_a_690_ = stack[6].m_obj;
lean_object* v_res_979_;
v_res_979_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
stack->m_obj
 = v_res_979_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_980_, lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
uint8_t v_pu_boxed_988_; lean_object* v_res_989_; 
v_pu_boxed_988_ = lean_unbox(v_pu_980_);
v_res_989_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_988_, v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec_ref(v_a_982_);
return v_res_989_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_binderName_999_; lean_object* v_type_1000_; uint8_t v_borrow_1001_; lean_object* v___y_1003_; 
v_binderName_999_ = lean_ctor_get(v_param_994_, 1);
lean_inc(v_binderName_999_);
v_type_1000_ = lean_ctor_get(v_param_994_, 2);
lean_inc_ref(v_type_1000_);
v_borrow_1001_ = lean_ctor_get_uint8(v_param_994_, sizeof(void*)*3);
lean_dec_ref(v_param_994_);
if (v_borrow_1001_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1003_ = v___x_1036_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_1003_ = v___x_1037_;
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_996_);
v___x_1005_ = l_Lean_pp_funBinderTypes;
v___x_1006_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1004_, v___x_1005_);
lean_dec_ref(v___x_1004_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v_type_1000_);
v___x_1007_ = 1;
v___x_1008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_999_, v___x_1007_);
lean_inc_ref(v___y_1003_);
v___x_1009_ = lean_string_append(v___y_1003_, v___x_1008_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1000_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1035_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1017_ = l_Lean_Name_toString(v_binderName_999_, v___x_1006_);
v___x_1018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
lean_inc_ref(v___y_1003_);
v___x_1021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___y_1003_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_1013_);
v___x_1024_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1025_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_1023_);
v___x_1027_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1024_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = 0;
v___x_1031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*1, v___x_1030_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1031_);
v___x_1033_ = v___x_1015_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_dec(v_binderName_999_);
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppParam___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_param_994_ = stack[0].m_obj;
lean_object* v_a_995_ = stack[1].m_obj;
lean_object* v_a_996_ = stack[2].m_obj;
lean_object* v_a_997_ = stack[3].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_994_, v_a_995_, v_a_996_, v_a_997_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1044_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1045_, lean_object* v_param_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1046_, v_a_1047_, v_a_1050_, v_a_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1045_ = stack[0].m_num;
lean_object* v_param_1046_ = stack[1].m_obj;
lean_object* v_a_1047_ = stack[2].m_obj;
lean_object* v_a_1048_ = stack[3].m_obj;
lean_object* v_a_1049_ = stack[4].m_obj;
lean_object* v_a_1050_ = stack[5].m_obj;
lean_object* v_a_1051_ = stack[6].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_1045_, v_param_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1055_, lean_object* v_param_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
uint8_t v_pu_boxed_1063_; lean_object* v_res_1064_; 
v_pu_boxed_1063_ = lean_unbox(v_pu_1055_);
v_res_1064_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1063_, v_param_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1064_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1065_, lean_object* v_params_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1074_ = lean_box(v_pu_1065_);
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1075_, 0, v___x_1074_);
v___x_1076_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1073_, v_params_1066_, v___x_1075_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
return v___x_1076_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1065_ = stack[0].m_num;
lean_object* v_params_1066_ = stack[1].m_obj;
lean_object* v_a_1067_ = stack[2].m_obj;
lean_object* v_a_1068_ = stack[3].m_obj;
lean_object* v_a_1069_ = stack[4].m_obj;
lean_object* v_a_1070_ = stack[5].m_obj;
lean_object* v_a_1071_ = stack[6].m_obj;
lean_object* v_res_1077_;
v_res_1077_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1065_, v_params_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
stack->m_obj
 = v_res_1077_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1078_, lean_object* v_params_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
uint8_t v_pu_boxed_1086_; lean_object* v_res_1087_; 
v_pu_boxed_1086_ = lean_unbox(v_pu_1078_);
v_res_1087_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1086_, v_params_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec_ref(v_params_1079_);
return v_res_1087_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1094_, lean_object* v_letDecl_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1099_);
v___x_1103_ = l_Lean_pp_letVarTypes;
v___x_1104_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1102_);
if (v___x_1104_ == 0)
{
lean_object* v_binderName_1105_; lean_object* v_value_1106_; lean_object* v___x_1107_; 
v_binderName_1105_ = lean_ctor_get(v_letDecl_1095_, 1);
lean_inc(v_binderName_1105_);
v_value_1106_ = lean_ctor_get(v_letDecl_1095_, 3);
lean_inc(v_value_1106_);
lean_dec_ref(v_letDecl_1095_);
v___x_1107_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1094_, v_value_1106_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1123_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1123_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1123_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1112_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1113_ = 1;
v___x_1114_ = l_Lean_Name_toString(v_binderName_1105_, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1112_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1119_);
v___x_1121_ = v___x_1110_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_dec(v_binderName_1105_);
return v___x_1107_;
}
}
else
{
lean_object* v_binderName_1124_; lean_object* v_type_1125_; lean_object* v_value_1126_; lean_object* v___x_1127_; 
v_binderName_1124_ = lean_ctor_get(v_letDecl_1095_, 1);
lean_inc(v_binderName_1124_);
v_type_1125_ = lean_ctor_get(v_letDecl_1095_, 2);
lean_inc_ref(v_type_1125_);
v_value_1126_ = lean_ctor_get(v_letDecl_1095_, 3);
lean_inc(v_value_1126_);
lean_dec_ref(v_letDecl_1095_);
v___x_1127_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1125_, v_a_1096_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1153_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1153_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1153_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1094_, v_value_1126_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1152_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1138_ = l_Lean_Name_toString(v_binderName_1124_, v___x_1104_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 3);
lean_ctor_set(v___x_1130_, 0, v___x_1138_);
v___x_1140_ = v___x_1130_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1137_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_a_1128_);
v___x_1145_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1147_);
v___x_1149_ = v___x_1135_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_del_object(v___x_1130_);
lean_dec(v_a_1128_);
lean_dec(v_binderName_1124_);
return v___x_1132_;
}
}
}
else
{
lean_dec(v_value_1126_);
lean_dec(v_binderName_1124_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1094_ = stack[0].m_num;
lean_object* v_letDecl_1095_ = stack[1].m_obj;
lean_object* v_a_1096_ = stack[2].m_obj;
lean_object* v_a_1097_ = stack[3].m_obj;
lean_object* v_a_1098_ = stack[4].m_obj;
lean_object* v_a_1099_ = stack[5].m_obj;
lean_object* v_a_1100_ = stack[6].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1094_, v_letDecl_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
stack->m_obj
 = v_res_1154_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_bs_1167_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1165_ = stack[0].m_num;
size_t v_i_1166_ = stack[1].m_num;
lean_object* v_bs_1167_ = stack[2].m_obj;
lean_object* v_res_1178_;
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1165_, v_i_1166_, v_bs_1167_);
stack->m_obj
 = v_res_1178_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_bs_1181_){
_start:
{
size_t v_sz_boxed_1182_; size_t v_i_boxed_1183_; lean_object* v_res_1184_; 
v_sz_boxed_1182_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1183_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1182_, v_i_boxed_1183_, v_bs_1181_);
return v_res_1184_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1185_, lean_object* v_ps_1186_, lean_object* v_type_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_Expr_isErased(v_type_1187_);
if (v___x_1191_ == 0)
{
if (v_pu_1185_ == 0)
{
size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_sz_1192_ = lean_array_size(v_ps_1186_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1192_, v___x_1193_, v_ps_1186_);
v___x_1195_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1187_, v___x_1194_, v_a_1188_, v_a_1189_);
lean_dec_ref(v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
lean_dec_ref(v_ps_1186_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_type_1187_);
return v___x_1196_;
}
}
else
{
lean_object* v___x_1197_; 
lean_dec_ref(v_ps_1186_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_type_1187_);
return v___x_1197_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_getFunType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1185_ = stack[0].m_num;
lean_object* v_ps_1186_ = stack[1].m_obj;
lean_object* v_type_1187_ = stack[2].m_obj;
lean_object* v_a_1188_ = stack[3].m_obj;
lean_object* v_a_1189_ = stack[4].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1185_, v_ps_1186_, v_type_1187_, v_a_1188_, v_a_1189_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1199_, lean_object* v_ps_1200_, lean_object* v_type_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
uint8_t v_pu_boxed_1205_; lean_object* v_res_1206_; 
v_pu_boxed_1205_ = lean_unbox(v_pu_1199_);
v_res_1206_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1205_, v_ps_1200_, v_type_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1206_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1231_, lean_object* v_alt_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
switch(lean_obj_tag(v_alt_1232_))
{
case 0:
{
lean_object* v_ctorName_1239_; lean_object* v_params_1240_; lean_object* v_code_1241_; lean_object* v___x_1242_; 
v_ctorName_1239_ = lean_ctor_get(v_alt_1232_, 0);
lean_inc(v_ctorName_1239_);
v_params_1240_ = lean_ctor_get(v_alt_1232_, 1);
lean_inc_ref(v_params_1240_);
v_code_1241_ = lean_ctor_get(v_alt_1232_, 2);
lean_inc_ref(v_code_1241_);
lean_dec_ref_known(v_alt_1232_, 3);
v___x_1242_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1231_, v_params_1240_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_params_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1268_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1268_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1268_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1231_, v_code_1241_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1267_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1267_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1267_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1252_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1253_ = 1;
v___x_1254_ = l_Lean_Name_toString(v_ctorName_1239_, v___x_1253_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 3);
lean_ctor_set(v___x_1245_, 0, v___x_1254_);
v___x_1256_ = v___x_1245_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1252_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1243_);
v___x_1259_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Std_Format_indentD(v_a_1248_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1262_);
v___x_1264_ = v___x_1250_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_del_object(v___x_1245_);
lean_dec(v_a_1243_);
lean_dec(v_ctorName_1239_);
return v___x_1247_;
}
}
}
else
{
lean_dec_ref(v_code_1241_);
lean_dec(v_ctorName_1239_);
return v___x_1242_;
}
}
case 1:
{
lean_object* v_info_1269_; lean_object* v_code_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1295_; 
v_info_1269_ = lean_ctor_get(v_alt_1232_, 0);
v_code_1270_ = lean_ctor_get(v_alt_1232_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_alt_1232_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1272_ = v_alt_1232_;
v_isShared_1273_ = v_isSharedCheck_1295_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_code_1270_);
lean_inc(v_info_1269_);
lean_dec(v_alt_1232_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1295_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1231_, v_code_1270_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1294_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1294_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1294_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_name_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v_name_1279_ = lean_ctor_get(v_info_1269_, 0);
lean_inc(v_name_1279_);
lean_dec_ref(v_info_1269_);
v___x_1280_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1281_ = 1;
v___x_1282_ = l_Lean_Name_toString(v_name_1279_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 5);
lean_ctor_set(v___x_1272_, 1, v___x_1283_);
lean_ctor_set(v___x_1272_, 0, v___x_1280_);
v___x_1285_ = v___x_1272_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1286_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Std_Format_indentD(v_a_1275_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1289_);
v___x_1291_ = v___x_1277_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_del_object(v___x_1272_);
lean_dec_ref(v_info_1269_);
return v___x_1274_;
}
}
}
default: 
{
lean_object* v_code_1296_; lean_object* v___x_1297_; 
v_code_1296_ = lean_ctor_get(v_alt_1232_, 0);
lean_inc_ref(v_code_1296_);
lean_dec_ref_known(v_alt_1232_, 1);
v___x_1297_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1231_, v_code_1296_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1308_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1308_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1308_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1302_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1303_ = l_Std_Format_indentD(v_a_1298_);
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1304_);
v___x_1306_ = v___x_1300_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppAlt_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1231_ = stack[0].m_num;
lean_object* v_alt_1232_ = stack[1].m_obj;
lean_object* v_a_1233_ = stack[2].m_obj;
lean_object* v_a_1234_ = stack[3].m_obj;
lean_object* v_a_1235_ = stack[4].m_obj;
lean_object* v_a_1236_ = stack[5].m_obj;
lean_object* v_a_1237_ = stack[6].m_obj;
lean_object* v_res_1309_;
v_res_1309_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_1231_, v_alt_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1310_, lean_object* v_alt_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
uint8_t v_pu_boxed_1318_; lean_object* v_res_1319_; 
v_pu_boxed_1318_ = lean_unbox(v_pu_1310_);
v_res_1319_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1318_, v_alt_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_a_1312_);
return v_res_1319_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1371_, lean_object* v_c_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
switch(lean_obj_tag(v_c_1372_))
{
case 0:
{
lean_object* v_decl_1379_; lean_object* v_k_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1402_; 
v_decl_1379_ = lean_ctor_get(v_c_1372_, 0);
v_k_1380_ = lean_ctor_get(v_c_1372_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1382_ = v_c_1372_;
v_isShared_1383_ = v_isSharedCheck_1402_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_k_1380_);
lean_inc(v_decl_1379_);
lean_dec(v_c_1372_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1402_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1371_, v_decl_1379_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1380_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1401_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 5);
lean_ctor_set(v___x_1382_, 1, v___x_1391_);
lean_ctor_set(v___x_1382_, 0, v_a_1385_);
v___x_1393_ = v___x_1382_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1394_ = lean_box(1);
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v_a_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1396_);
v___x_1398_ = v___x_1389_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_del_object(v___x_1382_);
return v___x_1386_;
}
}
else
{
lean_del_object(v___x_1382_);
lean_dec_ref(v_k_1380_);
return v___x_1384_;
}
}
}
case 1:
{
lean_object* v_decl_1403_; lean_object* v_k_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1428_; 
v_decl_1403_ = lean_ctor_get(v_c_1372_, 0);
v_k_1404_ = lean_ctor_get(v_c_1372_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1406_ = v_c_1372_;
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_k_1404_);
lean_inc(v_decl_1403_);
lean_dec(v_c_1372_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1371_, v_decl_1403_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1404_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1427_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1427_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1427_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 5);
lean_ctor_set(v___x_1406_, 1, v_a_1409_);
lean_ctor_set(v___x_1406_, 0, v___x_1415_);
v___x_1417_ = v___x_1406_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1409_);
v___x_1417_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1418_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_box(1);
v___x_1421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v_a_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1422_);
v___x_1424_ = v___x_1413_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_dec(v_a_1409_);
lean_del_object(v___x_1406_);
return v___x_1410_;
}
}
else
{
lean_del_object(v___x_1406_);
lean_dec_ref(v_k_1404_);
return v___x_1408_;
}
}
}
case 2:
{
lean_object* v_decl_1429_; lean_object* v_k_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_decl_1429_ = lean_ctor_get(v_c_1372_, 0);
v_k_1430_ = lean_ctor_get(v_c_1372_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1432_ = v_c_1372_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_k_1430_);
lean_inc(v_decl_1429_);
lean_dec(v_c_1372_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1371_, v_decl_1429_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1430_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1453_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 5);
lean_ctor_set(v___x_1432_, 1, v_a_1435_);
lean_ctor_set(v___x_1432_, 0, v___x_1441_);
v___x_1443_ = v___x_1432_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1435_);
v___x_1443_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1444_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_box(1);
v___x_1447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1448_);
v___x_1450_ = v___x_1439_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_dec(v_a_1435_);
lean_del_object(v___x_1432_);
return v___x_1436_;
}
}
else
{
lean_del_object(v___x_1432_);
lean_dec_ref(v_k_1430_);
return v___x_1434_;
}
}
}
case 3:
{
lean_object* v_fvarId_1455_; lean_object* v_args_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1476_; 
v_fvarId_1455_ = lean_ctor_get(v_c_1372_, 0);
v_args_1456_ = lean_ctor_get(v_c_1372_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1458_ = v_c_1372_;
v_isShared_1459_ = v_isSharedCheck_1476_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_args_1456_);
lean_inc(v_fvarId_1455_);
lean_dec(v_c_1372_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1476_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1455_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1371_, v_args_1456_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec_ref(v_args_1456_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1475_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 5);
lean_ctor_set(v___x_1458_, 1, v_a_1461_);
lean_ctor_set(v___x_1458_, 0, v___x_1467_);
v___x_1469_ = v___x_1458_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_a_1461_);
v___x_1469_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_a_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1470_);
v___x_1472_ = v___x_1465_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_dec(v_a_1461_);
lean_del_object(v___x_1458_);
return v___x_1462_;
}
}
else
{
lean_del_object(v___x_1458_);
lean_dec_ref(v_args_1456_);
return v___x_1460_;
}
}
}
case 4:
{
lean_object* v_cases_1477_; lean_object* v_resultType_1478_; lean_object* v_discr_1479_; lean_object* v_alts_1480_; lean_object* v___x_1481_; 
v_cases_1477_ = lean_ctor_get(v_c_1372_, 0);
lean_inc_ref(v_cases_1477_);
lean_dec_ref_known(v_c_1372_, 1);
v_resultType_1478_ = lean_ctor_get(v_cases_1477_, 1);
lean_inc_ref(v_resultType_1478_);
v_discr_1479_ = lean_ctor_get(v_cases_1477_, 2);
lean_inc(v_discr_1479_);
v_alts_1480_ = lean_ctor_get(v_cases_1477_, 3);
lean_inc_ref(v_alts_1480_);
lean_dec_ref(v_cases_1477_);
v___x_1481_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1479_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1478_, v_a_1373_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = lean_box(1);
v___x_1486_ = lean_box(v_pu_1371_);
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1487_, 0, v___x_1486_);
v___x_1488_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1485_, v_alts_1480_, v___x_1487_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec_ref(v_alts_1480_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1502_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1502_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1502_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1493_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_a_1482_);
v___x_1495_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v_a_1484_);
v___x_1498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_a_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1498_);
v___x_1500_ = v___x_1491_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_dec(v_a_1484_);
lean_dec(v_a_1482_);
return v___x_1488_;
}
}
else
{
lean_dec(v_a_1482_);
lean_dec_ref(v_alts_1480_);
return v___x_1483_;
}
}
else
{
lean_dec_ref(v_alts_1480_);
lean_dec_ref(v_resultType_1478_);
return v___x_1481_;
}
}
case 5:
{
lean_object* v_fvarId_1503_; lean_object* v___x_1504_; 
v_fvarId_1503_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1503_);
lean_dec_ref_known(v_c_1372_, 1);
v___x_1504_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1503_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
return v___x_1504_;
}
}
case 6:
{
lean_object* v_type_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1537_; 
v_type_1515_ = lean_ctor_get(v_c_1372_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1517_ = v_c_1372_;
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_type_1515_);
lean_dec(v_c_1372_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1376_);
v___x_1520_ = l_Lean_pp_all;
v___x_1521_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1519_, v___x_1520_);
lean_dec_ref(v___x_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec_ref(v_type_1515_);
v___x_1522_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1522_);
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
else
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1517_);
v___x_1526_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1515_, v_a_1373_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_a_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
return v___x_1526_;
}
}
}
}
case 7:
{
lean_object* v_fvarId_1538_; lean_object* v_i_1539_; lean_object* v_y_1540_; lean_object* v_k_1541_; lean_object* v___x_1542_; 
v_fvarId_1538_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1538_);
v_i_1539_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_i_1539_);
v_y_1540_ = lean_ctor_get(v_c_1372_, 2);
lean_inc(v_y_1540_);
v_k_1541_ = lean_ctor_get(v_c_1372_, 3);
lean_inc_ref(v_k_1541_);
lean_dec_ref_known(v_c_1372_, 4);
v___x_1542_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1538_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1540_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1575_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1541_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1574_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1574_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1574_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1554_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1543_);
v___x_1556_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Nat_reprFast(v_i_1539_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 3);
lean_ctor_set(v___x_1547_, 0, v___x_1558_);
v___x_1560_ = v___x_1547_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1545_);
v___x_1565_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_box(1);
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_a_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1569_);
v___x_1571_ = v___x_1552_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_del_object(v___x_1547_);
lean_dec(v_a_1545_);
lean_dec(v_a_1543_);
lean_dec(v_i_1539_);
return v___x_1549_;
}
}
}
else
{
lean_dec(v_a_1543_);
lean_dec_ref(v_k_1541_);
lean_dec(v_i_1539_);
return v___x_1544_;
}
}
else
{
lean_dec_ref(v_k_1541_);
lean_dec(v_y_1540_);
lean_dec(v_i_1539_);
return v___x_1542_;
}
}
case 8:
{
lean_object* v_fvarId_1576_; lean_object* v_i_1577_; lean_object* v_y_1578_; lean_object* v_k_1579_; lean_object* v___x_1580_; 
v_fvarId_1576_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1576_);
v_i_1577_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_i_1577_);
v_y_1578_ = lean_ctor_get(v_c_1372_, 2);
lean_inc(v_y_1578_);
v_k_1579_ = lean_ctor_get(v_c_1372_, 3);
lean_inc_ref(v_k_1579_);
lean_dec_ref_known(v_c_1372_, 4);
v___x_1580_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1576_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1578_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1613_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1613_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1613_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1579_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1612_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1612_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1612_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1592_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v_a_1581_);
v___x_1594_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Nat_reprFast(v_i_1577_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 3);
lean_ctor_set(v___x_1585_, 0, v___x_1596_);
v___x_1598_ = v___x_1585_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1595_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v_a_1583_);
v___x_1603_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_box(1);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v_a_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1607_);
v___x_1609_ = v___x_1590_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_del_object(v___x_1585_);
lean_dec(v_a_1583_);
lean_dec(v_a_1581_);
lean_dec(v_i_1577_);
return v___x_1587_;
}
}
}
else
{
lean_dec(v_a_1581_);
lean_dec_ref(v_k_1579_);
lean_dec(v_i_1577_);
return v___x_1582_;
}
}
else
{
lean_dec_ref(v_k_1579_);
lean_dec(v_y_1578_);
lean_dec(v_i_1577_);
return v___x_1580_;
}
}
case 9:
{
lean_object* v_fvarId_1614_; lean_object* v_i_1615_; lean_object* v_offset_1616_; lean_object* v_y_1617_; lean_object* v_ty_1618_; lean_object* v_k_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_fvarId_1614_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1614_);
v_i_1615_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_i_1615_);
v_offset_1616_ = lean_ctor_get(v_c_1372_, 2);
lean_inc(v_offset_1616_);
v_y_1617_ = lean_ctor_get(v_c_1372_, 3);
lean_inc(v_y_1617_);
v_ty_1618_ = lean_ctor_get(v_c_1372_, 4);
lean_inc_ref(v_ty_1618_);
v_k_1619_ = lean_ctor_get(v_c_1372_, 5);
lean_inc_ref(v_k_1619_);
lean_dec_ref_known(v_c_1372_, 6);
v___x_1620_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1376_);
v___x_1621_ = l_Lean_pp_letVarTypes;
v___x_1622_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1620_, v___x_1621_);
lean_dec_ref(v___x_1620_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
lean_dec_ref(v_ty_1618_);
v___x_1623_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1614_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1667_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1667_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1667_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1617_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1666_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1666_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1666_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1619_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1665_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1665_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1665_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1638_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1624_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Nat_reprFast(v_i_1615_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 3);
lean_ctor_set(v___x_1631_, 0, v___x_1642_);
v___x_1644_ = v___x_1631_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1641_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Nat_reprFast(v_offset_1616_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 3);
lean_ctor_set(v___x_1626_, 0, v___x_1648_);
v___x_1650_ = v___x_1626_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1647_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_a_1629_);
v___x_1655_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_box(1);
v___x_1658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_a_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1659_);
v___x_1661_ = v___x_1636_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
else
{
lean_del_object(v___x_1631_);
lean_dec(v_a_1629_);
lean_del_object(v___x_1626_);
lean_dec(v_a_1624_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1633_;
}
}
}
else
{
lean_del_object(v___x_1626_);
lean_dec(v_a_1624_);
lean_dec_ref(v_k_1619_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1628_;
}
}
}
else
{
lean_dec_ref(v_k_1619_);
lean_dec(v_y_1617_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1623_;
}
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1614_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1618_, v_a_1373_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1717_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1717_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1717_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1617_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1716_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1716_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1716_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1619_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1715_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1715_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1715_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1685_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v_a_1669_);
v___x_1687_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Nat_reprFast(v_i_1615_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 3);
lean_ctor_set(v___x_1678_, 0, v___x_1689_);
v___x_1691_ = v___x_1678_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1688_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Nat_reprFast(v_offset_1616_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 3);
lean_ctor_set(v___x_1673_, 0, v___x_1695_);
v___x_1697_ = v___x_1673_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1694_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_a_1671_);
v___x_1702_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v_a_1676_);
v___x_1705_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_box(1);
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v_a_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1709_);
v___x_1711_ = v___x_1683_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
lean_del_object(v___x_1678_);
lean_dec(v_a_1676_);
lean_del_object(v___x_1673_);
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1680_;
}
}
}
else
{
lean_del_object(v___x_1673_);
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
lean_dec_ref(v_k_1619_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1675_;
}
}
}
else
{
lean_dec(v_a_1669_);
lean_dec_ref(v_k_1619_);
lean_dec(v_y_1617_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1670_;
}
}
else
{
lean_dec_ref(v_k_1619_);
lean_dec_ref(v_ty_1618_);
lean_dec(v_y_1617_);
lean_dec(v_offset_1616_);
lean_dec(v_i_1615_);
return v___x_1668_;
}
}
}
case 10:
{
lean_object* v_fvarId_1718_; lean_object* v_cidx_1719_; lean_object* v_k_1720_; lean_object* v___x_1721_; 
v_fvarId_1718_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1718_);
v_cidx_1719_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_cidx_1719_);
v_k_1720_ = lean_ctor_get(v_c_1372_, 2);
lean_inc_ref(v_k_1720_);
lean_dec_ref_known(v_c_1372_, 3);
v___x_1721_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1718_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1749_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1749_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1749_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1720_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1748_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1748_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1748_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1731_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_a_1722_);
v___x_1733_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Nat_reprFast(v_cidx_1719_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 3);
lean_ctor_set(v___x_1724_, 0, v___x_1735_);
v___x_1737_ = v___x_1724_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1734_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_box(1);
v___x_1742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1727_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1743_);
v___x_1745_ = v___x_1729_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_del_object(v___x_1724_);
lean_dec(v_a_1722_);
lean_dec(v_cidx_1719_);
return v___x_1726_;
}
}
}
else
{
lean_dec_ref(v_k_1720_);
lean_dec(v_cidx_1719_);
return v___x_1721_;
}
}
case 11:
{
lean_object* v_fvarId_1750_; lean_object* v_n_1751_; uint8_t v_check_1752_; uint8_t v_persistent_1753_; lean_object* v_k_1754_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1823_; 
v_fvarId_1750_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1750_);
v_n_1751_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_n_1751_);
v_check_1752_ = lean_ctor_get_uint8(v_c_1372_, sizeof(void*)*3);
v_persistent_1753_ = lean_ctor_get_uint8(v_c_1372_, sizeof(void*)*3 + 1);
v_k_1754_ = lean_ctor_get(v_c_1372_, 2);
lean_inc_ref(v_k_1754_);
lean_dec_ref_known(v_c_1372_, 3);
if (v_persistent_1753_ == 0)
{
lean_object* v___x_1826_; 
v___x_1826_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1823_ = v___x_1826_;
goto v___jp_1822_;
}
else
{
lean_object* v___x_1827_; 
v___x_1827_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___y_1823_ = v___x_1827_;
goto v___jp_1822_;
}
v___jp_1755_:
{
lean_object* v_ann_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
lean_inc_ref(v___y_1756_);
v_ann_1758_ = lean_string_append(v___y_1756_, v___y_1757_);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_dec_eq(v_n_1751_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1750_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1793_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1793_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1793_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1754_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1792_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1792_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1792_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1771_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1772_ = l_Nat_reprFast(v_n_1751_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 3);
lean_ctor_set(v___x_1764_, 0, v___x_1772_);
v___x_1774_ = v___x_1764_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1771_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_ann_1758_);
v___x_1779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_a_1762_);
v___x_1783_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_box(1);
v___x_1786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v_a_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1787_);
v___x_1789_ = v___x_1769_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_del_object(v___x_1764_);
lean_dec(v_a_1762_);
lean_dec_ref(v_ann_1758_);
lean_dec(v_n_1751_);
return v___x_1766_;
}
}
}
else
{
lean_dec_ref(v_ann_1758_);
lean_dec_ref(v_k_1754_);
lean_dec(v_n_1751_);
return v___x_1761_;
}
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_n_1751_);
v___x_1794_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1750_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1821_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1754_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1820_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1820_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1820_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 3);
lean_ctor_set(v___x_1797_, 0, v_ann_1758_);
v___x_1806_ = v___x_1797_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_ann_1758_);
v___x_1806_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_a_1795_);
v___x_1811_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_box(1);
v___x_1814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_a_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1815_);
v___x_1817_ = v___x_1802_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_del_object(v___x_1797_);
lean_dec(v_a_1795_);
lean_dec_ref(v_ann_1758_);
return v___x_1799_;
}
}
}
else
{
lean_dec_ref(v_ann_1758_);
lean_dec_ref(v_k_1754_);
return v___x_1794_;
}
}
}
v___jp_1822_:
{
if (v_check_1752_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
v___y_1756_ = v___y_1823_;
v___y_1757_ = v___x_1824_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1756_ = v___y_1823_;
v___y_1757_ = v___x_1825_;
goto v___jp_1755_;
}
}
}
case 12:
{
lean_object* v_fvarId_1828_; lean_object* v_n_1829_; uint8_t v_check_1830_; uint8_t v_persistent_1831_; lean_object* v_objs_x3f_1832_; lean_object* v_k_1833_; lean_object* v_ann_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v_ann_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_ann_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; 
v_fvarId_1828_ = lean_ctor_get(v_c_1372_, 0);
lean_inc(v_fvarId_1828_);
v_n_1829_ = lean_ctor_get(v_c_1372_, 1);
lean_inc(v_n_1829_);
v_check_1830_ = lean_ctor_get_uint8(v_c_1372_, sizeof(void*)*4);
v_persistent_1831_ = lean_ctor_get_uint8(v_c_1372_, sizeof(void*)*4 + 1);
v_objs_x3f_1832_ = lean_ctor_get(v_c_1372_, 2);
lean_inc(v_objs_x3f_1832_);
v_k_1833_ = lean_ctor_get(v_c_1372_, 3);
lean_inc_ref(v_k_1833_);
lean_dec_ref_known(v_c_1372_, 4);
if (v_persistent_1831_ == 0)
{
lean_object* v_ann_1927_; 
v_ann_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v_ann_1919_ = v_ann_1927_;
v___y_1920_ = v_a_1373_;
v___y_1921_ = v_a_1374_;
v___y_1922_ = v_a_1375_;
v___y_1923_ = v_a_1376_;
v___y_1924_ = v_a_1377_;
goto v___jp_1918_;
}
else
{
lean_object* v_ann_1928_; 
v_ann_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v_ann_1919_ = v_ann_1928_;
v___y_1920_ = v_a_1373_;
v___y_1921_ = v_a_1374_;
v___y_1922_ = v_a_1375_;
v___y_1923_ = v_a_1376_;
v___y_1924_ = v_a_1377_;
goto v___jp_1918_;
}
v___jp_1834_:
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_dec_eq(v_n_1829_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1828_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1875_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1875_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1875_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1833_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1874_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1874_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1874_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1854_ = l_Nat_reprFast(v_n_1829_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 3);
lean_ctor_set(v___x_1846_, 0, v___x_1854_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1853_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_ann_1835_);
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1844_);
v___x_1865_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_box(1);
v___x_1868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v_a_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1869_);
v___x_1871_ = v___x_1851_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec_ref(v_ann_1835_);
lean_dec(v_n_1829_);
return v___x_1848_;
}
}
}
else
{
lean_dec_ref(v_ann_1835_);
lean_dec_ref(v_k_1833_);
lean_dec(v_n_1829_);
return v___x_1843_;
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v_n_1829_);
v___x_1876_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1828_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1903_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1903_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1903_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1833_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1902_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1902_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1902_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 3);
lean_ctor_set(v___x_1879_, 0, v_ann_1835_);
v___x_1888_ = v___x_1879_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_ann_1835_);
v___x_1888_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1886_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v_a_1877_);
v___x_1893_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_box(1);
v___x_1896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_a_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1897_);
v___x_1899_ = v___x_1884_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_del_object(v___x_1879_);
lean_dec(v_a_1877_);
lean_dec_ref(v_ann_1835_);
return v___x_1881_;
}
}
}
else
{
lean_dec_ref(v_ann_1835_);
lean_dec_ref(v_k_1833_);
return v___x_1876_;
}
}
}
v___jp_1904_:
{
if (lean_obj_tag(v_objs_x3f_1832_) == 1)
{
lean_object* v_val_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_ann_1917_; 
v_val_1911_ = lean_ctor_get(v_objs_x3f_1832_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v_objs_x3f_1832_, 1);
v___x_1912_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0));
v___x_1913_ = l_Nat_reprFast(v_val_1911_);
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__40));
v___x_1916_ = lean_string_append(v___x_1914_, v___x_1915_);
v_ann_1917_ = lean_string_append(v_ann_1905_, v___x_1916_);
lean_dec_ref(v___x_1916_);
v_ann_1835_ = v_ann_1917_;
v___y_1836_ = v___y_1906_;
v___y_1837_ = v___y_1907_;
v___y_1838_ = v___y_1908_;
v___y_1839_ = v___y_1909_;
v___y_1840_ = v___y_1910_;
goto v___jp_1834_;
}
else
{
lean_dec(v_objs_x3f_1832_);
v_ann_1835_ = v_ann_1905_;
v___y_1836_ = v___y_1906_;
v___y_1837_ = v___y_1907_;
v___y_1838_ = v___y_1908_;
v___y_1839_ = v___y_1909_;
v___y_1840_ = v___y_1910_;
goto v___jp_1834_;
}
}
v___jp_1918_:
{
if (v_check_1830_ == 0)
{
lean_object* v___x_1925_; lean_object* v_ann_1926_; 
v___x_1925_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
lean_inc_ref(v_ann_1919_);
v_ann_1926_ = lean_string_append(v_ann_1919_, v___x_1925_);
v_ann_1905_ = v_ann_1926_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
goto v___jp_1904_;
}
else
{
lean_inc_ref(v_ann_1919_);
v_ann_1905_ = v_ann_1919_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
goto v___jp_1904_;
}
}
}
default: 
{
lean_object* v_fvarId_1929_; lean_object* v_k_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1954_; 
v_fvarId_1929_ = lean_ctor_get(v_c_1372_, 0);
v_k_1930_ = lean_ctor_get(v_c_1372_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_c_1372_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1932_ = v_c_1372_;
v_isShared_1933_ = v_isSharedCheck_1954_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_k_1930_);
lean_inc(v_fvarId_1929_);
lean_dec(v_c_1372_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1954_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1929_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_k_1930_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1953_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__42));
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 5);
lean_ctor_set(v___x_1932_, 1, v_a_1935_);
lean_ctor_set(v___x_1932_, 0, v___x_1941_);
v___x_1943_ = v___x_1932_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_a_1935_);
v___x_1943_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1944_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_box(1);
v___x_1947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_a_1937_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1948_);
v___x_1950_ = v___x_1939_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_dec(v_a_1935_);
lean_del_object(v___x_1932_);
return v___x_1936_;
}
}
else
{
lean_del_object(v___x_1932_);
lean_dec_ref(v_k_1930_);
return v___x_1934_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1371_ = stack[0].m_num;
lean_object* v_c_1372_ = stack[1].m_obj;
lean_object* v_a_1373_ = stack[2].m_obj;
lean_object* v_a_1374_ = stack[3].m_obj;
lean_object* v_a_1375_ = stack[4].m_obj;
lean_object* v_a_1376_ = stack[5].m_obj;
lean_object* v_a_1377_ = stack[6].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1371_, v_c_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
stack->m_obj
 = v_res_1955_;
}
lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1956_, lean_object* v_funDecl_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_binderName_1964_; lean_object* v_params_1965_; lean_object* v_type_1966_; lean_object* v_value_1967_; lean_object* v___x_1968_; 
v_binderName_1964_ = lean_ctor_get(v_funDecl_1957_, 1);
lean_inc(v_binderName_1964_);
v_params_1965_ = lean_ctor_get(v_funDecl_1957_, 2);
lean_inc_ref(v_params_1965_);
v_type_1966_ = lean_ctor_get(v_funDecl_1957_, 3);
lean_inc_ref(v_type_1966_);
v_value_1967_ = lean_ctor_get(v_funDecl_1957_, 4);
lean_inc_ref(v_value_1967_);
lean_dec_ref(v_funDecl_1957_);
v___x_1968_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1956_, v_params_1965_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1956_, v_params_1965_, v_type_1966_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1971_, v_a_1958_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1999_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1999_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1999_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1956_, v_value_1967_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1998_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1998_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1998_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1982_ = 1;
v___x_1983_ = l_Lean_Name_toString(v_binderName_1964_, v___x_1982_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 3);
lean_ctor_set(v___x_1975_, 0, v___x_1983_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set(v___x_1986_, 1, v_a_1969_);
v___x_1987_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_a_1973_);
v___x_1990_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Std_Format_indentD(v_a_1978_);
v___x_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1993_);
v___x_1995_ = v___x_1980_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
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
lean_del_object(v___x_1975_);
lean_dec(v_a_1973_);
lean_dec(v_a_1969_);
lean_dec(v_binderName_1964_);
return v___x_1977_;
}
}
}
else
{
lean_dec(v_a_1969_);
lean_dec_ref(v_value_1967_);
lean_dec(v_binderName_1964_);
return v___x_1972_;
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1969_);
lean_dec_ref(v_value_1967_);
lean_dec(v_binderName_1964_);
v_a_2000_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1970_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1970_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_dec_ref(v_value_1967_);
lean_dec_ref(v_type_1966_);
lean_dec_ref(v_params_1965_);
lean_dec(v_binderName_1964_);
return v___x_1968_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1956_ = stack[0].m_num;
lean_object* v_funDecl_1957_ = stack[1].m_obj;
lean_object* v_a_1958_ = stack[2].m_obj;
lean_object* v_a_1959_ = stack[3].m_obj;
lean_object* v_a_1960_ = stack[4].m_obj;
lean_object* v_a_1961_ = stack[5].m_obj;
lean_object* v_a_1962_ = stack[6].m_obj;
lean_object* v_res_2008_;
v_res_2008_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1956_, v_funDecl_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
stack->m_obj
 = v_res_2008_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_2009_, lean_object* v_funDecl_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
uint8_t v_pu_boxed_2017_; lean_object* v_res_2018_; 
v_pu_boxed_2017_ = lean_unbox(v_pu_2009_);
v_res_2018_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_2017_, v_funDecl_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_2019_, lean_object* v_c_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
uint8_t v_pu_boxed_2027_; lean_object* v_res_2028_; 
v_pu_boxed_2027_ = lean_unbox(v_pu_2019_);
v_res_2028_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_2027_, v_c_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2028_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_2032_, lean_object* v_b_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
if (lean_obj_tag(v_b_2033_) == 0)
{
lean_object* v_code_2040_; lean_object* v___x_2041_; 
v_code_2040_ = lean_ctor_get(v_b_2033_, 0);
lean_inc_ref(v_code_2040_);
lean_dec_ref_known(v_b_2033_, 1);
v___x_2041_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_2032_, v_code_2040_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
return v___x_2041_;
}
else
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_isSharedCheck_2049_ = !lean_is_exclusive(v_b_2033_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_b_2033_, 0);
lean_dec(v_unused_2050_);
v___x_2043_ = v_b_2033_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_b_2033_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_ppDeclValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2032_ = stack[0].m_num;
lean_object* v_b_2033_ = stack[1].m_obj;
lean_object* v_a_2034_ = stack[2].m_obj;
lean_object* v_a_2035_ = stack[3].m_obj;
lean_object* v_a_2036_ = stack[4].m_obj;
lean_object* v_a_2037_ = stack[5].m_obj;
lean_object* v_a_2038_ = stack[6].m_obj;
lean_object* v_res_2051_;
v_res_2051_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2032_, v_b_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
stack->m_obj
 = v_res_2051_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_2052_, lean_object* v_b_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
uint8_t v_pu_boxed_2060_; lean_object* v_res_2061_; 
v_pu_boxed_2060_ = lean_unbox(v_pu_2052_);
v_res_2061_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_2060_, v_b_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec_ref(v_a_2054_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_2062_, lean_object* v_opt_2063_){
_start:
{
lean_object* v_name_2064_; lean_object* v_defValue_2065_; lean_object* v_map_2066_; lean_object* v___x_2067_; 
v_name_2064_ = lean_ctor_get(v_opt_2063_, 0);
v_defValue_2065_ = lean_ctor_get(v_opt_2063_, 1);
v_map_2066_ = lean_ctor_get(v_opts_2062_, 0);
v___x_2067_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2066_, v_name_2064_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_inc(v_defValue_2065_);
return v_defValue_2065_;
}
else
{
lean_object* v_val_2068_; 
v_val_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v___x_2067_, 1);
if (lean_obj_tag(v_val_2068_) == 3)
{
lean_object* v_v_2069_; 
v_v_2069_ = lean_ctor_get(v_val_2068_, 0);
lean_inc(v_v_2069_);
lean_dec_ref_known(v_val_2068_, 1);
return v_v_2069_;
}
else
{
lean_dec(v_val_2068_);
lean_inc(v_defValue_2065_);
return v_defValue_2065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_2070_, lean_object* v_opt_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_2070_, v_opt_2071_);
lean_dec_ref(v_opt_2071_);
lean_dec_ref(v_opts_2070_);
return v_res_2072_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(lean_object* v_o_2076_, lean_object* v_k_2077_, uint8_t v_v_2078_){
_start:
{
lean_object* v_map_2079_; uint8_t v_hasTrace_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2094_; 
v_map_2079_ = lean_ctor_get(v_o_2076_, 0);
v_hasTrace_2080_ = lean_ctor_get_uint8(v_o_2076_, sizeof(void*)*1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_o_2076_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2082_ = v_o_2076_;
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_map_2079_);
lean_dec(v_o_2076_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2084_, 0, v_v_2078_);
lean_inc(v_k_2077_);
v___x_2085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2077_, v___x_2084_, v_map_2079_);
if (v_hasTrace_2080_ == 0)
{
lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2089_; 
v___x_2086_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1));
v___x_2087_ = l_Lean_Name_isPrefixOf(v___x_2086_, v_k_2077_);
lean_dec(v_k_2077_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2089_ = v___x_2082_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2085_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*1, v___x_2087_);
return v___x_2089_;
}
}
else
{
lean_object* v___x_2092_; 
lean_dec(v_k_2077_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2092_ = v___x_2082_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2093_, sizeof(void*)*1, v_hasTrace_2080_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2076_ = stack[0].m_obj;
lean_object* v_k_2077_ = stack[1].m_obj;
uint8_t v_v_2078_ = stack[2].m_num;
lean_object* v_res_2095_;
v_res_2095_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_o_2076_, v_k_2077_, v_v_2078_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___boxed(lean_object* v_o_2096_, lean_object* v_k_2097_, lean_object* v_v_2098_){
_start:
{
uint8_t v_v_boxed_2099_; lean_object* v_res_2100_; 
v_v_boxed_2099_ = lean_unbox(v_v_2098_);
v_res_2100_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_o_2096_, v_k_2097_, v_v_boxed_2099_);
return v_res_2100_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_2101_, lean_object* v_opt_2102_, uint8_t v_val_2103_){
_start:
{
lean_object* v_name_2104_; lean_object* v___x_2105_; 
v_name_2104_ = lean_ctor_get(v_opt_2102_, 0);
lean_inc(v_name_2104_);
lean_dec_ref(v_opt_2102_);
v___x_2105_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_opts_2101_, v_name_2104_, v_val_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2101_ = stack[0].m_obj;
lean_object* v_opt_2102_ = stack[1].m_obj;
uint8_t v_val_2103_ = stack[2].m_num;
lean_object* v_res_2106_;
v_res_2106_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2101_, v_opt_2102_, v_val_2103_);
stack->m_obj
 = v_res_2106_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_2107_, lean_object* v_opt_2108_, lean_object* v_val_2109_){
_start:
{
uint8_t v_val_boxed_2110_; lean_object* v_res_2111_; 
v_val_boxed_2110_ = lean_unbox(v_val_2109_);
v_res_2111_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2107_, v_opt_2108_, v_val_boxed_2110_);
return v_res_2111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
return v___x_2115_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint16_t v___y_2123_; lean_object* v___y_2124_; lean_object* v_fileName_2125_; lean_object* v_fileMap_2126_; lean_object* v_currNamespace_2127_; lean_object* v_openDecls_2128_; lean_object* v_initHeartbeats_2129_; lean_object* v_maxHeartbeats_2130_; lean_object* v_quotContext_2131_; lean_object* v_currMacroScope_2132_; lean_object* v_cancelTk_x3f_2133_; lean_object* v_inheritedTraceOptions_2134_; lean_object* v_currRecDepth_2135_; lean_object* v_ref_2136_; uint8_t v_suppressElabErrors_2137_; uint8_t v_isRecordingDeps_2138_; lean_object* v___y_2139_; lean_object* v_toCold_2159_; lean_object* v_currRecDepth_2160_; lean_object* v_ref_2161_; uint8_t v_suppressElabErrors_2162_; uint8_t v_isRecordingDeps_2163_; lean_object* v_fileName_2164_; lean_object* v_fileMap_2165_; lean_object* v_options_2166_; lean_object* v_currNamespace_2167_; lean_object* v_openDecls_2168_; lean_object* v_initHeartbeats_2169_; lean_object* v_maxHeartbeats_2170_; lean_object* v_quotContext_2171_; lean_object* v_currMacroScope_2172_; lean_object* v_cancelTk_x3f_2173_; lean_object* v_inheritedTraceOptions_2174_; uint16_t v___y_2176_; lean_object* v___y_2177_; uint8_t v___y_2178_; lean_object* v___y_2201_; 
v_toCold_2159_ = lean_ctor_get(v_a_2119_, 0);
v_currRecDepth_2160_ = lean_ctor_get(v_a_2119_, 1);
v_ref_2161_ = lean_ctor_get(v_a_2119_, 2);
v_suppressElabErrors_2162_ = lean_ctor_get_uint8(v_a_2119_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2163_ = lean_ctor_get_uint8(v_a_2119_, sizeof(void*)*3 + 3);
v_fileName_2164_ = lean_ctor_get(v_toCold_2159_, 0);
v_fileMap_2165_ = lean_ctor_get(v_toCold_2159_, 1);
v_options_2166_ = lean_ctor_get(v_toCold_2159_, 2);
v_currNamespace_2167_ = lean_ctor_get(v_toCold_2159_, 4);
v_openDecls_2168_ = lean_ctor_get(v_toCold_2159_, 5);
v_initHeartbeats_2169_ = lean_ctor_get(v_toCold_2159_, 6);
v_maxHeartbeats_2170_ = lean_ctor_get(v_toCold_2159_, 7);
v_quotContext_2171_ = lean_ctor_get(v_toCold_2159_, 8);
v_currMacroScope_2172_ = lean_ctor_get(v_toCold_2159_, 9);
v_cancelTk_x3f_2173_ = lean_ctor_get(v_toCold_2159_, 10);
v_inheritedTraceOptions_2174_ = lean_ctor_get(v_toCold_2159_, 11);
if (v_isRecordingDeps_2163_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = l_Lean_pp_sanitizeNames;
lean_inc_ref(v_options_2166_);
v___x_2213_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_options_2166_, v___x_2212_, v_isRecordingDeps_2163_);
v___y_2201_ = v___x_2213_;
goto v___jp_2200_;
}
else
{
lean_object* v___x_2214_; 
lean_inc_ref(v_options_2166_);
v___x_2214_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2166_);
v___y_2201_ = v___x_2214_;
goto v___jp_2200_;
}
v___jp_2122_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = l_Lean_maxRecDepth;
v___x_2141_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v___y_2124_, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2142_, 0, v_fileName_2125_);
lean_ctor_set(v___x_2142_, 1, v_fileMap_2126_);
lean_ctor_set(v___x_2142_, 2, v___y_2124_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
lean_ctor_set(v___x_2142_, 4, v_currNamespace_2127_);
lean_ctor_set(v___x_2142_, 5, v_openDecls_2128_);
lean_ctor_set(v___x_2142_, 6, v_initHeartbeats_2129_);
lean_ctor_set(v___x_2142_, 7, v_maxHeartbeats_2130_);
lean_ctor_set(v___x_2142_, 8, v_quotContext_2131_);
lean_ctor_set(v___x_2142_, 9, v_currMacroScope_2132_);
lean_ctor_set(v___x_2142_, 10, v_cancelTk_x3f_2133_);
lean_ctor_set(v___x_2142_, 11, v_inheritedTraceOptions_2134_);
lean_inc(v_ref_2136_);
lean_inc(v_currRecDepth_2135_);
v___x_2143_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_currRecDepth_2135_);
lean_ctor_set(v___x_2143_, 2, v_ref_2136_);
lean_ctor_set_uint16(v___x_2143_, sizeof(void*)*3, v___y_2123_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*3 + 2, v_suppressElabErrors_2137_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*3 + 3, v_isRecordingDeps_2138_);
v___x_2144_ = lean_st_ref_get(v_a_2118_);
v___x_2145_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2117_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v_lctx_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v_lctx_2147_ = lean_ctor_get(v___x_2144_, 0);
lean_inc_ref(v_lctx_2147_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_unbox(v_a_2146_);
lean_dec(v_a_2146_);
v___x_2149_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2147_, v___x_2148_);
lean_dec_ref(v_lctx_2147_);
lean_inc(v___y_2139_);
lean_inc(v_a_2118_);
lean_inc_ref(v_a_2117_);
v___x_2150_ = lean_apply_6(v_x_2116_, v___x_2149_, v_a_2117_, v_a_2118_, v___x_2143_, v___y_2139_, lean_box(0));
return v___x_2150_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v___x_2144_);
lean_dec_ref_known(v___x_2143_, 3);
lean_dec_ref(v_x_2116_);
v_a_2151_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2145_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2145_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
v___jp_2175_:
{
lean_object* v___x_2179_; lean_object* v_env_2180_; lean_object* v_nextMacroScope_2181_; lean_object* v_ngen_2182_; lean_object* v_auxDeclNGen_2183_; lean_object* v_traceState_2184_; lean_object* v_recordedDeps_2185_; lean_object* v_messages_2186_; lean_object* v_infoState_2187_; lean_object* v_snapshotTasks_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2198_; 
v___x_2179_ = lean_st_ref_take(v_a_2120_);
v_env_2180_ = lean_ctor_get(v___x_2179_, 0);
v_nextMacroScope_2181_ = lean_ctor_get(v___x_2179_, 1);
v_ngen_2182_ = lean_ctor_get(v___x_2179_, 2);
v_auxDeclNGen_2183_ = lean_ctor_get(v___x_2179_, 3);
v_traceState_2184_ = lean_ctor_get(v___x_2179_, 4);
v_recordedDeps_2185_ = lean_ctor_get(v___x_2179_, 6);
v_messages_2186_ = lean_ctor_get(v___x_2179_, 7);
v_infoState_2187_ = lean_ctor_get(v___x_2179_, 8);
v_snapshotTasks_2188_ = lean_ctor_get(v___x_2179_, 9);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v___x_2179_, 5);
lean_dec(v_unused_2199_);
v___x_2190_ = v___x_2179_;
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_snapshotTasks_2188_);
lean_inc(v_infoState_2187_);
lean_inc(v_messages_2186_);
lean_inc(v_recordedDeps_2185_);
lean_inc(v_traceState_2184_);
lean_inc(v_auxDeclNGen_2183_);
lean_inc(v_ngen_2182_);
lean_inc(v_nextMacroScope_2181_);
lean_inc(v_env_2180_);
lean_dec(v___x_2179_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = l_Lean_Kernel_enableDiag(v_env_2180_, v___y_2178_);
v___x_2193_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 5, v___x_2193_);
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2195_ = v___x_2190_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_nextMacroScope_2181_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_ngen_2182_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_auxDeclNGen_2183_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_traceState_2184_);
lean_ctor_set(v_reuseFailAlloc_2197_, 5, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2197_, 6, v_recordedDeps_2185_);
lean_ctor_set(v_reuseFailAlloc_2197_, 7, v_messages_2186_);
lean_ctor_set(v_reuseFailAlloc_2197_, 8, v_infoState_2187_);
lean_ctor_set(v_reuseFailAlloc_2197_, 9, v_snapshotTasks_2188_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_st_ref_put(v_a_2120_, v___x_2195_);
lean_inc_ref(v_inheritedTraceOptions_2174_);
lean_inc(v_cancelTk_x3f_2173_);
lean_inc(v_currMacroScope_2172_);
lean_inc(v_quotContext_2171_);
lean_inc(v_maxHeartbeats_2170_);
lean_inc(v_initHeartbeats_2169_);
lean_inc(v_openDecls_2168_);
lean_inc(v_currNamespace_2167_);
lean_inc_ref(v_fileMap_2165_);
lean_inc_ref(v_fileName_2164_);
v___y_2123_ = v___y_2176_;
v___y_2124_ = v___y_2177_;
v_fileName_2125_ = v_fileName_2164_;
v_fileMap_2126_ = v_fileMap_2165_;
v_currNamespace_2127_ = v_currNamespace_2167_;
v_openDecls_2128_ = v_openDecls_2168_;
v_initHeartbeats_2129_ = v_initHeartbeats_2169_;
v_maxHeartbeats_2130_ = v_maxHeartbeats_2170_;
v_quotContext_2131_ = v_quotContext_2171_;
v_currMacroScope_2132_ = v_currMacroScope_2172_;
v_cancelTk_x3f_2133_ = v_cancelTk_x3f_2173_;
v_inheritedTraceOptions_2134_ = v_inheritedTraceOptions_2174_;
v_currRecDepth_2135_ = v_currRecDepth_2160_;
v_ref_2136_ = v_ref_2161_;
v_suppressElabErrors_2137_ = v_suppressElabErrors_2162_;
v_isRecordingDeps_2138_ = v_isRecordingDeps_2163_;
v___y_2139_ = v_a_2120_;
goto v___jp_2122_;
}
}
}
v___jp_2200_:
{
uint16_t v___x_2202_; lean_object* v___x_2203_; lean_object* v_env_2204_; uint8_t v___x_2205_; uint16_t v___x_2206_; uint16_t v___x_2207_; uint16_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2202_ = l_Lean_OptionFlags_ofOptions(v___y_2201_);
v___x_2203_ = lean_st_ref_get(v_a_2120_);
v_env_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_env_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2204_);
lean_dec_ref(v_env_2204_);
v___x_2206_ = 512;
v___x_2207_ = lean_uint16_land(v___x_2202_, v___x_2206_);
v___x_2208_ = 0;
v___x_2209_ = lean_uint16_dec_eq(v___x_2207_, v___x_2208_);
if (v___x_2209_ == 0)
{
if (v___x_2205_ == 0)
{
uint8_t v___x_2210_; 
v___x_2210_ = 1;
v___y_2176_ = v___x_2202_;
v___y_2177_ = v___y_2201_;
v___y_2178_ = v___x_2210_;
goto v___jp_2175_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2174_);
lean_inc(v_cancelTk_x3f_2173_);
lean_inc(v_currMacroScope_2172_);
lean_inc(v_quotContext_2171_);
lean_inc(v_maxHeartbeats_2170_);
lean_inc(v_initHeartbeats_2169_);
lean_inc(v_openDecls_2168_);
lean_inc(v_currNamespace_2167_);
lean_inc_ref(v_fileMap_2165_);
lean_inc_ref(v_fileName_2164_);
v___y_2123_ = v___x_2202_;
v___y_2124_ = v___y_2201_;
v_fileName_2125_ = v_fileName_2164_;
v_fileMap_2126_ = v_fileMap_2165_;
v_currNamespace_2127_ = v_currNamespace_2167_;
v_openDecls_2128_ = v_openDecls_2168_;
v_initHeartbeats_2129_ = v_initHeartbeats_2169_;
v_maxHeartbeats_2130_ = v_maxHeartbeats_2170_;
v_quotContext_2131_ = v_quotContext_2171_;
v_currMacroScope_2132_ = v_currMacroScope_2172_;
v_cancelTk_x3f_2133_ = v_cancelTk_x3f_2173_;
v_inheritedTraceOptions_2134_ = v_inheritedTraceOptions_2174_;
v_currRecDepth_2135_ = v_currRecDepth_2160_;
v_ref_2136_ = v_ref_2161_;
v_suppressElabErrors_2137_ = v_suppressElabErrors_2162_;
v_isRecordingDeps_2138_ = v_isRecordingDeps_2163_;
v___y_2139_ = v_a_2120_;
goto v___jp_2122_;
}
}
else
{
if (v___x_2205_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2174_);
lean_inc(v_cancelTk_x3f_2173_);
lean_inc(v_currMacroScope_2172_);
lean_inc(v_quotContext_2171_);
lean_inc(v_maxHeartbeats_2170_);
lean_inc(v_initHeartbeats_2169_);
lean_inc(v_openDecls_2168_);
lean_inc(v_currNamespace_2167_);
lean_inc_ref(v_fileMap_2165_);
lean_inc_ref(v_fileName_2164_);
v___y_2123_ = v___x_2202_;
v___y_2124_ = v___y_2201_;
v_fileName_2125_ = v_fileName_2164_;
v_fileMap_2126_ = v_fileMap_2165_;
v_currNamespace_2127_ = v_currNamespace_2167_;
v_openDecls_2128_ = v_openDecls_2168_;
v_initHeartbeats_2129_ = v_initHeartbeats_2169_;
v_maxHeartbeats_2130_ = v_maxHeartbeats_2170_;
v_quotContext_2131_ = v_quotContext_2171_;
v_currMacroScope_2132_ = v_currMacroScope_2172_;
v_cancelTk_x3f_2133_ = v_cancelTk_x3f_2173_;
v_inheritedTraceOptions_2134_ = v_inheritedTraceOptions_2174_;
v_currRecDepth_2135_ = v_currRecDepth_2160_;
v_ref_2136_ = v_ref_2161_;
v_suppressElabErrors_2137_ = v_suppressElabErrors_2162_;
v_isRecordingDeps_2138_ = v_isRecordingDeps_2163_;
v___y_2139_ = v_a_2120_;
goto v___jp_2122_;
}
else
{
uint8_t v___x_2211_; 
v___x_2211_ = 0;
v___y_2176_ = v___x_2202_;
v___y_2177_ = v___y_2201_;
v___y_2178_ = v___x_2211_;
goto v___jp_2175_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2116_ = stack[0].m_obj;
lean_object* v_a_2117_ = stack[1].m_obj;
lean_object* v_a_2118_ = stack[2].m_obj;
lean_object* v_a_2119_ = stack[3].m_obj;
lean_object* v_a_2120_ = stack[4].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2222_;
}
}
lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2223_, lean_object* v_x_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PP_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2224_ = stack[1].m_obj;
lean_object* v_a_2225_ = stack[2].m_obj;
lean_object* v_a_2226_ = stack[3].m_obj;
lean_object* v_a_2227_ = stack[4].m_obj;
lean_object* v_a_2228_ = stack[5].m_obj;
lean_object* v_res_2231_;
v_res_2231_ = l_Lean_Compiler_LCNF_PP_run(lean_box(0), v_x_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
stack->m_obj
 = v_res_2231_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_x_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2232_, v_x_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2239_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2240_, lean_object* v_code_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_box(v_pu_2240_);
v___x_2248_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2248_, 0, v___x_2247_);
lean_closure_set(v___x_2248_, 1, v_code_2241_);
v___x_2249_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2248_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2249_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2240_ = stack[0].m_num;
lean_object* v_code_2241_ = stack[1].m_obj;
lean_object* v_a_2242_ = stack[2].m_obj;
lean_object* v_a_2243_ = stack[3].m_obj;
lean_object* v_a_2244_ = stack[4].m_obj;
lean_object* v_a_2245_ = stack[5].m_obj;
lean_object* v_res_2250_;
v_res_2250_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2240_, v_code_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
stack->m_obj
 = v_res_2250_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2251_, lean_object* v_code_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
uint8_t v_pu_boxed_2258_; lean_object* v_res_2259_; 
v_pu_boxed_2258_ = lean_unbox(v_pu_2251_);
v_res_2259_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2258_, v_code_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2259_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2260_, lean_object* v_e_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_box(v_pu_2260_);
v___x_2268_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2268_, 0, v___x_2267_);
lean_closure_set(v___x_2268_, 1, v_e_2261_);
v___x_2269_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2268_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2269_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2260_ = stack[0].m_num;
lean_object* v_e_2261_ = stack[1].m_obj;
lean_object* v_a_2262_ = stack[2].m_obj;
lean_object* v_a_2263_ = stack[3].m_obj;
lean_object* v_a_2264_ = stack[4].m_obj;
lean_object* v_a_2265_ = stack[5].m_obj;
lean_object* v_res_2270_;
v_res_2270_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_2260_, v_e_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
stack->m_obj
 = v_res_2270_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2271_, lean_object* v_e_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
uint8_t v_pu_boxed_2278_; lean_object* v_res_2279_; 
v_pu_boxed_2278_ = lean_unbox(v_pu_2271_);
v_res_2279_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2278_, v_e_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2279_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2283_, lean_object* v_params_2284_, lean_object* v_type_2285_, lean_object* v_value_2286_, lean_object* v_name_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2283_, v_params_2284_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2283_, v_params_2284_, v_type_2285_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2297_, v___y_2288_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2327_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2327_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2327_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2283_, v_value_2286_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2326_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2326_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2326_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2308_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2309_ = 1;
v___x_2310_ = l_Lean_Name_toString(v_name_2287_, v___x_2309_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 3);
lean_ctor_set(v___x_2301_, 0, v___x_2310_);
v___x_2312_ = v___x_2301_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2308_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v_a_2295_);
v___x_2315_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_a_2299_);
v___x_2318_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Std_Format_indentD(v_a_2304_);
v___x_2321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2321_);
v___x_2323_ = v___x_2306_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
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
lean_del_object(v___x_2301_);
lean_dec(v_a_2299_);
lean_dec(v_a_2295_);
lean_dec(v_name_2287_);
return v___x_2303_;
}
}
}
else
{
lean_dec(v_a_2295_);
lean_dec(v_name_2287_);
lean_dec_ref(v_value_2286_);
return v___x_2298_;
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2295_);
lean_dec(v_name_2287_);
lean_dec_ref(v_value_2286_);
v_a_2328_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2296_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2296_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_dec(v_name_2287_);
lean_dec_ref(v_value_2286_);
lean_dec_ref(v_type_2285_);
lean_dec_ref(v_params_2284_);
return v___x_2294_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppDecl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2283_ = stack[0].m_num;
lean_object* v_params_2284_ = stack[1].m_obj;
lean_object* v_type_2285_ = stack[2].m_obj;
lean_object* v_value_2286_ = stack[3].m_obj;
lean_object* v_name_2287_ = stack[4].m_obj;
lean_object* v___y_2288_ = stack[5].m_obj;
lean_object* v___y_2289_ = stack[6].m_obj;
lean_object* v___y_2290_ = stack[7].m_obj;
lean_object* v___y_2291_ = stack[8].m_obj;
lean_object* v___y_2292_ = stack[9].m_obj;
lean_object* v_res_2336_;
v_res_2336_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_2283_, v_params_2284_, v_type_2285_, v_value_2286_, v_name_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
stack->m_obj
 = v_res_2336_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2337_, lean_object* v_params_2338_, lean_object* v_type_2339_, lean_object* v_value_2340_, lean_object* v_name_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v_pu_boxed_2348_; lean_object* v_res_2349_; 
v_pu_boxed_2348_ = lean_unbox(v_pu_2337_);
v_res_2349_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2348_, v_params_2338_, v_type_2339_, v_value_2340_, v_name_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2349_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2350_, lean_object* v_decl_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_toSignature_2357_; lean_object* v_value_2358_; lean_object* v_name_2359_; lean_object* v_type_2360_; lean_object* v_params_2361_; lean_object* v___x_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
v_toSignature_2357_ = lean_ctor_get(v_decl_2351_, 0);
lean_inc_ref(v_toSignature_2357_);
v_value_2358_ = lean_ctor_get(v_decl_2351_, 1);
lean_inc_ref(v_value_2358_);
lean_dec_ref(v_decl_2351_);
v_name_2359_ = lean_ctor_get(v_toSignature_2357_, 0);
lean_inc(v_name_2359_);
v_type_2360_ = lean_ctor_get(v_toSignature_2357_, 2);
lean_inc_ref(v_type_2360_);
v_params_2361_ = lean_ctor_get(v_toSignature_2357_, 3);
lean_inc_ref(v_params_2361_);
lean_dec_ref(v_toSignature_2357_);
v___x_2362_ = lean_box(v_pu_2350_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2363_, 0, v___x_2362_);
lean_closure_set(v___f_2363_, 1, v_params_2361_);
lean_closure_set(v___f_2363_, 2, v_type_2360_);
lean_closure_set(v___f_2363_, 3, v_value_2358_);
lean_closure_set(v___f_2363_, 4, v_name_2359_);
v___x_2364_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2363_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
return v___x_2364_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2350_ = stack[0].m_num;
lean_object* v_decl_2351_ = stack[1].m_obj;
lean_object* v_a_2352_ = stack[2].m_obj;
lean_object* v_a_2353_ = stack[3].m_obj;
lean_object* v_a_2354_ = stack[4].m_obj;
lean_object* v_a_2355_ = stack[5].m_obj;
lean_object* v_res_2365_;
v_res_2365_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2350_, v_decl_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
stack->m_obj
 = v_res_2365_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2366_, lean_object* v_decl_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
uint8_t v_pu_boxed_2373_; lean_object* v_res_2374_; 
v_pu_boxed_2373_ = lean_unbox(v_pu_2366_);
v_res_2374_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2373_, v_decl_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
return v_res_2374_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2375_, lean_object* v_decl_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2375_, v_decl_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2393_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2388_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v_a_2384_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2389_);
v___x_2391_ = v___x_2386_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
else
{
return v___x_2383_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppFunDecl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2375_ = stack[0].m_num;
lean_object* v_decl_2376_ = stack[1].m_obj;
lean_object* v___y_2377_ = stack[2].m_obj;
lean_object* v___y_2378_ = stack[3].m_obj;
lean_object* v___y_2379_ = stack[4].m_obj;
lean_object* v___y_2380_ = stack[5].m_obj;
lean_object* v___y_2381_ = stack[6].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_2375_, v_decl_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2395_, lean_object* v_decl_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_pu_boxed_2403_; lean_object* v_res_2404_; 
v_pu_boxed_2403_ = lean_unbox(v_pu_2395_);
v_res_2404_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2403_, v_decl_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2404_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2405_, lean_object* v_decl_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_box(v_pu_2405_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2413_, 0, v___x_2412_);
lean_closure_set(v___f_2413_, 1, v_decl_2406_);
v___x_2414_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2413_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
return v___x_2414_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2405_ = stack[0].m_num;
lean_object* v_decl_2406_ = stack[1].m_obj;
lean_object* v_a_2407_ = stack[2].m_obj;
lean_object* v_a_2408_ = stack[3].m_obj;
lean_object* v_a_2409_ = stack[4].m_obj;
lean_object* v_a_2410_ = stack[5].m_obj;
lean_object* v_res_2415_;
v_res_2415_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_2405_, v_decl_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
stack->m_obj
 = v_res_2415_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2416_, lean_object* v_decl_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
uint8_t v_pu_boxed_2423_; lean_object* v_res_2424_; 
v_pu_boxed_2423_ = lean_unbox(v_pu_2416_);
v_res_2424_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2423_, v_decl_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2424_;
}
}
lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2425_, lean_object* v_val_2426_, lean_object* v_a_x3f_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_st_ref_swap(v_a_2425_, v_val_2426_);
lean_dec(v___x_2430_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2425_ = stack[0].m_obj;
lean_object* v_val_2426_ = stack[1].m_obj;
lean_object* v_a_x3f_2427_ = stack[2].m_obj;
lean_object* v_res_2432_;
v_res_2432_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2425_, v_val_2426_, v_a_x3f_2427_);
stack->m_obj
 = v_res_2432_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2433_, lean_object* v_val_2434_, lean_object* v_a_x3f_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2433_, v_val_2434_, v_a_x3f_2435_);
lean_dec(v_a_x3f_2435_);
lean_dec(v_a_2433_);
return v_res_2437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_unsigned_to_nat(16u);
v___x_2440_ = lean_mk_array(v___x_2439_, v___x_2438_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2441_);
return v___x_2443_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2445_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
lean_ctor_set(v___x_2445_, 2, v___x_2444_);
lean_ctor_set(v___x_2445_, 3, v___x_2444_);
lean_ctor_set(v___x_2445_, 4, v___x_2444_);
lean_ctor_set(v___x_2445_, 5, v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2446_);
return v___x_2448_;
}
}
lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2449_, lean_object* v_x_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_r_2456_; 
v___x_2454_ = lean_st_ref_get(v_a_2452_);
v___x_2455_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2456_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2450_, v___x_2455_, v_phase_2449_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v_r_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2473_; 
v_a_2457_ = lean_ctor_get(v_r_2456_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_r_2456_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2459_ = v_r_2456_;
v_isShared_2460_ = v_isSharedCheck_2473_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v_r_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2473_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
lean_inc(v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set_tag(v___x_2459_, 1);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v___x_2463_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2452_, v___x_2454_, v___x_2462_);
lean_dec_ref(v___x_2462_);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2463_, 0);
lean_dec(v_unused_2471_);
v___x_2465_ = v___x_2463_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v___x_2463_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v_a_2457_);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2457_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2474_ = lean_ctor_get(v_r_2456_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v_r_2456_, 1);
v___x_2475_ = lean_box(0);
v___x_2476_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2452_, v___x_2454_, v___x_2475_);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2484_);
v___x_2478_ = v___x_2476_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v___x_2476_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 1);
lean_ctor_set(v___x_2478_, 0, v_a_2474_);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2474_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2449_ = stack[0].m_num;
lean_object* v_x_2450_ = stack[1].m_obj;
lean_object* v_a_2451_ = stack[2].m_obj;
lean_object* v_a_2452_ = stack[3].m_obj;
lean_object* v_res_2485_;
v_res_2485_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2449_, v_x_2450_, v_a_2451_, v_a_2452_);
stack->m_obj
 = v_res_2485_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2486_, lean_object* v_x_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
uint8_t v_phase_boxed_2491_; lean_object* v_res_2492_; 
v_phase_boxed_2491_ = lean_unbox(v_phase_2486_);
v_res_2492_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2491_, v_x_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2492_;
}
}
lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2493_, uint8_t v_phase_2494_, lean_object* v_x_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2494_, v_x_2495_, v_a_2496_, v_a_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2494_ = stack[1].m_num;
lean_object* v_x_2495_ = stack[2].m_obj;
lean_object* v_a_2496_ = stack[3].m_obj;
lean_object* v_a_2497_ = stack[4].m_obj;
lean_object* v_res_2500_;
v_res_2500_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_box(0), v_phase_2494_, v_x_2495_, v_a_2496_, v_a_2497_);
stack->m_obj
 = v_res_2500_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2501_, lean_object* v_phase_2502_, lean_object* v_x_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
uint8_t v_phase_boxed_2507_; lean_object* v_res_2508_; 
v_phase_boxed_2507_ = lean_unbox(v_phase_2502_);
v_res_2508_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2501_, v_phase_boxed_2507_, v_x_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
return v_res_2508_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2509_, lean_object* v_decl_2510_, lean_object* v___x_2511_, uint8_t v___x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2509_, v_decl_2510_, v___x_2511_, v___x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2509_, v_a_2519_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2520_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
v_a_2521_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2518_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2518_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppDecl_x27___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2509_ = stack[0].m_num;
lean_object* v_decl_2510_ = stack[1].m_obj;
lean_object* v___x_2511_ = stack[2].m_obj;
uint8_t v___x_2512_ = stack[3].m_num;
lean_object* v___y_2513_ = stack[4].m_obj;
lean_object* v___y_2514_ = stack[5].m_obj;
lean_object* v___y_2515_ = stack[6].m_obj;
lean_object* v___y_2516_ = stack[7].m_obj;
lean_object* v_res_2529_;
v_res_2529_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_2509_, v_decl_2510_, v___x_2511_, v___x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
stack->m_obj
 = v_res_2529_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2530_, lean_object* v_decl_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v_pu_boxed_2539_; uint8_t v___x_100__boxed_2540_; lean_object* v_res_2541_; 
v_pu_boxed_2539_ = lean_unbox(v_pu_2530_);
v___x_100__boxed_2540_ = lean_unbox(v___x_2533_);
v_res_2541_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2539_, v_decl_2531_, v___x_2532_, v___x_100__boxed_2540_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2541_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2542_, lean_object* v_decl_2543_, uint8_t v_phase_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; 
v___x_2548_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2549_ = 0;
v___x_2550_ = lean_box(v_pu_2542_);
v___x_2551_ = lean_box(v___x_2549_);
v___f_2552_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2552_, 0, v___x_2550_);
lean_closure_set(v___f_2552_, 1, v_decl_2543_);
lean_closure_set(v___f_2552_, 2, v___x_2548_);
lean_closure_set(v___f_2552_, 3, v___x_2551_);
v___x_2553_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2544_, v___f_2552_, v_a_2545_, v_a_2546_);
return v___x_2553_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppDecl_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2542_ = stack[0].m_num;
lean_object* v_decl_2543_ = stack[1].m_obj;
uint8_t v_phase_2544_ = stack[2].m_num;
lean_object* v_a_2545_ = stack[3].m_obj;
lean_object* v_a_2546_ = stack[4].m_obj;
lean_object* v_res_2554_;
v_res_2554_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_2542_, v_decl_2543_, v_phase_2544_, v_a_2545_, v_a_2546_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2555_, lean_object* v_decl_2556_, lean_object* v_phase_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
uint8_t v_pu_boxed_2561_; uint8_t v_phase_boxed_2562_; lean_object* v_res_2563_; 
v_pu_boxed_2561_ = lean_unbox(v_pu_2555_);
v_phase_boxed_2562_ = lean_unbox(v_phase_2557_);
v_res_2563_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2561_, v_decl_2556_, v_phase_boxed_2562_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2563_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2564_, lean_object* v_code_2565_, lean_object* v___x_2566_, uint8_t v___x_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2564_, v_code_2565_, v___x_2566_, v___x_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2564_, v_a_2574_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2575_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2573_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2573_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppCode_x27___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2564_ = stack[0].m_num;
lean_object* v_code_2565_ = stack[1].m_obj;
lean_object* v___x_2566_ = stack[2].m_obj;
uint8_t v___x_2567_ = stack[3].m_num;
lean_object* v___y_2568_ = stack[4].m_obj;
lean_object* v___y_2569_ = stack[5].m_obj;
lean_object* v___y_2570_ = stack[6].m_obj;
lean_object* v___y_2571_ = stack[7].m_obj;
lean_object* v_res_2584_;
v_res_2584_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_2564_, v_code_2565_, v___x_2566_, v___x_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
stack->m_obj
 = v_res_2584_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2585_, lean_object* v_code_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v_pu_boxed_2594_; uint8_t v___x_100__boxed_2595_; lean_object* v_res_2596_; 
v_pu_boxed_2594_ = lean_unbox(v_pu_2585_);
v___x_100__boxed_2595_ = lean_unbox(v___x_2588_);
v_res_2596_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2594_, v_code_2586_, v___x_2587_, v___x_100__boxed_2595_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2596_;
}
}
lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2597_, lean_object* v_code_2598_, uint8_t v_phase_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; 
v___x_2603_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2604_ = 0;
v___x_2605_ = lean_box(v_pu_2597_);
v___x_2606_ = lean_box(v___x_2604_);
v___f_2607_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2607_, 0, v___x_2605_);
lean_closure_set(v___f_2607_, 1, v_code_2598_);
lean_closure_set(v___f_2607_, 2, v___x_2603_);
lean_closure_set(v___f_2607_, 3, v___x_2606_);
v___x_2608_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2599_, v___f_2607_, v_a_2600_, v_a_2601_);
return v___x_2608_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ppCode_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2597_ = stack[0].m_num;
lean_object* v_code_2598_ = stack[1].m_obj;
uint8_t v_phase_2599_ = stack[2].m_num;
lean_object* v_a_2600_ = stack[3].m_obj;
lean_object* v_a_2601_ = stack[4].m_obj;
lean_object* v_res_2609_;
v_res_2609_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_2597_, v_code_2598_, v_phase_2599_, v_a_2600_, v_a_2601_);
stack->m_obj
 = v_res_2609_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2610_, lean_object* v_code_2611_, lean_object* v_phase_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
uint8_t v_pu_boxed_2616_; uint8_t v_phase_boxed_2617_; lean_object* v_res_2618_; 
v_pu_boxed_2616_ = lean_unbox(v_pu_2610_);
v_phase_boxed_2617_ = lean_unbox(v_phase_2612_);
v_res_2618_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2616_, v_code_2611_, v_phase_boxed_2617_, v_a_2613_, v_a_2614_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2618_;
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

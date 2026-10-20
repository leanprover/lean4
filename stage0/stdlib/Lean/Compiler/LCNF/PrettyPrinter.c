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
static uint64_t _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_300_; uint64_t v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2(void){
_start:
{
uint64_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_uint64_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1);
v___x_303_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set_uint64(v___x_304_, sizeof(void*)*1, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_311_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_ctor_set(v___x_313_, 3, v___x_312_);
lean_ctor_set(v___x_313_, 4, v___x_311_);
lean_ctor_set(v___x_313_, 5, v___x_311_);
lean_ctor_set(v___x_313_, 6, v___x_311_);
lean_ctor_set(v___x_313_, 7, v___x_311_);
lean_ctor_set(v___x_313_, 8, v___x_311_);
lean_ctor_set(v___x_313_, 9, v___x_311_);
lean_ctor_set(v___x_313_, 10, v___x_311_);
lean_ctor_set(v___x_313_, 11, v___x_310_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_315_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_ctor_set(v___x_315_, 3, v___x_314_);
lean_ctor_set(v___x_315_, 4, v___x_314_);
lean_ctor_set(v___x_315_, 5, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_unsigned_to_nat(32u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9(void){
_start:
{
size_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = ((size_t)5ULL);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_unsigned_to_nat(32u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
v___x_324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
lean_ctor_set(v___x_324_, 2, v___x_320_);
lean_ctor_set(v___x_324_, 3, v___x_320_);
lean_ctor_set_usize(v___x_324_, 4, v___x_319_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
lean_ctor_set(v___x_326_, 4, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10);
v___x_328_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
v___x_329_ = lean_box(1);
v___x_330_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
v___x_331_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
v___x_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
lean_ctor_set(v___x_332_, 3, v___x_328_);
lean_ctor_set(v___x_332_, 4, v___x_327_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* v_e_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_338_ = lean_box(1);
v___x_339_ = 0;
v___x_340_ = 1;
v___x_341_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3));
v___x_344_ = lean_box(0);
lean_inc_ref(v_a_334_);
v___x_345_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_345_, 0, v___x_341_);
lean_ctor_set(v___x_345_, 1, v___x_338_);
lean_ctor_set(v___x_345_, 2, v_a_334_);
lean_ctor_set(v___x_345_, 3, v___x_343_);
lean_ctor_set(v___x_345_, 4, v___x_344_);
lean_ctor_set(v___x_345_, 5, v___x_342_);
lean_ctor_set(v___x_345_, 6, v___x_344_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7, v___x_339_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 1, v___x_339_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 2, v___x_339_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 3, v___x_340_);
v___x_346_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11);
v___x_347_ = lean_st_mk_ref(v___x_346_);
v___x_348_ = l_Lean_Meta_ppExpr(v_e_333_, v___x_345_, v___x_347_, v_a_335_, v_a_336_);
lean_dec_ref_known(v___x_345_, 7);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_st_ref_get(v___x_347_);
lean_dec(v___x_347_);
lean_dec(v___x_353_);
if (v_isShared_352_ == 0)
{
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_349_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_dec(v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_364_, v_a_365_, v_a_368_, v_a_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* v_opts_380_, lean_object* v_opt_381_){
_start:
{
lean_object* v_name_382_; lean_object* v_defValue_383_; lean_object* v_map_384_; lean_object* v___x_385_; 
v_name_382_ = lean_ctor_get(v_opt_381_, 0);
v_defValue_383_ = lean_ctor_get(v_opt_381_, 1);
v_map_384_ = lean_ctor_get(v_opts_380_, 0);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_384_, v_name_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_defValue_383_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; 
v_val_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_385_, 1);
if (lean_obj_tag(v_val_387_) == 1)
{
uint8_t v_v_388_; 
v_v_388_ = lean_ctor_get_uint8(v_val_387_, 0);
lean_dec_ref_known(v_val_387_, 0);
return v_v_388_;
}
else
{
uint8_t v___x_389_; 
lean_dec(v_val_387_);
v___x_389_ = lean_unbox(v_defValue_383_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* v_opts_390_, lean_object* v_opt_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_390_, v_opt_391_);
lean_dec_ref(v_opt_391_);
lean_dec_ref(v_opts_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_nat_to_int(v_a_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
v___x_405_ = lean_string_length(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
v___x_407_ = lean_nat_to_int(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
switch(lean_obj_tag(v_e_412_))
{
case 0:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
case 1:
{
lean_object* v_fvarId_421_; lean_object* v___x_422_; 
v_fvarId_421_ = lean_ctor_get(v_e_412_, 0);
lean_inc(v_fvarId_421_);
lean_dec_ref_known(v_e_412_, 1);
v___x_422_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_421_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_422_;
}
default: 
{
lean_object* v_expr_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_459_; 
v_expr_423_ = lean_ctor_get(v_e_412_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_e_412_);
if (v_isSharedCheck_459_ == 0)
{
v___x_425_ = v_e_412_;
v_isShared_426_ = v_isSharedCheck_459_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_expr_423_);
lean_dec(v_e_412_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_459_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_416_);
v___x_428_ = l_Lean_pp_explicit;
v___x_429_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_427_, v___x_428_);
lean_dec_ref(v___x_427_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_expr_423_);
v___x_430_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 0);
lean_ctor_set(v___x_425_, 0, v___x_430_);
v___x_432_ = v___x_425_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
uint8_t v___x_434_; 
lean_del_object(v___x_425_);
v___x_434_ = l_Lean_Expr_isConst(v_expr_423_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_Expr_isProp(v_expr_423_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Expr_isType0(v_expr_423_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Expr_isFVar(v_expr_423_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_423_, v_a_413_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_454_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_454_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_443_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_444_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_a_439_);
v___x_446_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_443_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_450_);
v___x_452_ = v___x_441_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
return v___x_438_;
}
}
else
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_423_, v_a_413_, v_a_416_, v_a_417_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_423_, v_a_413_, v_a_416_, v_a_417_);
return v___x_456_;
}
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_423_, v_a_413_, v_a_416_, v_a_417_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_423_, v_a_413_, v_a_416_, v_a_417_);
return v___x_458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t v_pu_468_, lean_object* v_e_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* v_pu_477_, lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
uint8_t v_pu_boxed_485_; lean_object* v_res_486_; 
v_pu_boxed_485_ = lean_unbox(v_pu_477_);
v_res_486_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_boxed_485_, v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t v_pu_487_, lean_object* v_args_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_496_ = lean_box(v_pu_487_);
v___x_497_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(v___x_497_, 0, v___x_496_);
v___x_498_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_495_, v_args_488_, v___x_497_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* v_pu_499_, lean_object* v_args_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v_pu_boxed_507_; lean_object* v_res_508_; 
v_pu_boxed_507_ = lean_unbox(v_pu_499_);
v_res_508_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_boxed_507_, v_args_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec_ref(v_args_500_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* v_lit_509_){
_start:
{
uint64_t v_v_512_; 
switch(lean_obj_tag(v_lit_509_))
{
case 0:
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_526_; 
v_val_517_ = lean_ctor_get(v_lit_509_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_lit_509_);
if (v_isSharedCheck_526_ == 0)
{
v___x_519_ = v_lit_509_;
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v_lit_509_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = l_Nat_reprFast(v_val_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 3);
lean_ctor_set(v___x_519_, 0, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_525_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
}
case 1:
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_val_527_ = lean_ctor_get(v_lit_509_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_lit_509_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v_lit_509_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v_lit_509_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = l_String_quote(v_val_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 3);
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
case 2:
{
uint8_t v_val_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_val_537_ = lean_ctor_get_uint8(v_lit_509_, 0);
lean_dec_ref_known(v_lit_509_, 0);
v___x_538_ = lean_uint8_to_nat(v_val_537_);
v___x_539_ = l_Nat_reprFast(v___x_538_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
case 3:
{
uint16_t v_val_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_val_542_ = lean_ctor_get_uint16(v_lit_509_, 0);
lean_dec_ref_known(v_lit_509_, 0);
v___x_543_ = lean_uint16_to_nat(v_val_542_);
v___x_544_ = l_Nat_reprFast(v___x_543_);
v___x_545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
case 4:
{
uint32_t v_val_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_val_547_ = lean_ctor_get_uint32(v_lit_509_, 0);
lean_dec_ref_known(v_lit_509_, 0);
v___x_548_ = lean_uint32_to_nat(v_val_547_);
v___x_549_ = l_Nat_reprFast(v___x_548_);
v___x_550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
default: 
{
uint64_t v_val_552_; 
v_val_552_ = lean_ctor_get_uint64(v_lit_509_, 0);
lean_dec_ref(v_lit_509_);
v_v_512_ = v_val_552_;
goto v___jp_511_;
}
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_uint64_to_nat(v_v_512_);
v___x_514_ = l_Nat_reprFast(v___x_513_);
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* v_lit_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* v_lit_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_556_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* v_lit_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* v_x_584_){
_start:
{
lean_object* v_name_585_; lean_object* v_cidx_586_; lean_object* v_usize_587_; lean_object* v_ssize_588_; lean_object* v_r_590_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_r_604_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_name_585_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_name_585_);
v_cidx_586_ = lean_ctor_get(v_x_584_, 1);
lean_inc(v_cidx_586_);
v_usize_587_ = lean_ctor_get(v_x_584_, 3);
lean_inc(v_usize_587_);
v_ssize_588_ = lean_ctor_get(v_x_584_, 4);
lean_inc(v_ssize_588_);
lean_dec_ref(v_x_584_);
v___x_601_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
v___x_602_ = l_Nat_reprFast(v_cidx_586_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v_r_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_604_, 0, v___x_601_);
lean_ctor_set(v_r_604_, 1, v___x_603_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_lt(v___x_615_, v_usize_587_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_lt(v___x_615_, v_ssize_588_);
if (v___x_617_ == 0)
{
lean_dec(v_ssize_588_);
lean_dec(v_usize_587_);
v_r_590_ = v_r_604_;
goto v___jp_589_;
}
else
{
goto v___jp_605_;
}
}
else
{
goto v___jp_605_;
}
v___jp_589_:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = lean_name_eq(v_name_585_, v___x_591_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_r_600_; 
v___x_593_ = 1;
v___x_594_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v_r_590_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Name_toString(v_name_585_, v___x_593_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v_r_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_600_, 0, v___x_598_);
lean_ctor_set(v_r_600_, 1, v___x_599_);
return v_r_600_;
}
else
{
lean_dec(v_name_585_);
return v_r_590_;
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_r_614_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v_r_604_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Nat_reprFast(v_usize_587_);
v___x_609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_606_);
v___x_612_ = l_Nat_reprFast(v_ssize_588_);
v___x_613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v_r_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_614_, 0, v___x_611_);
lean_ctor_set(v_r_614_, 1, v___x_613_);
v_r_590_ = v_r_614_;
goto v___jp_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_667_, lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
switch(lean_obj_tag(v_e_668_))
{
case 0:
{
lean_object* v_value_675_; lean_object* v___x_676_; 
v_value_675_ = lean_ctor_get(v_e_668_, 0);
lean_inc_ref(v_value_675_);
lean_dec_ref_known(v_e_668_, 1);
v___x_676_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_675_);
return v___x_676_;
}
case 1:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
case 2:
{
lean_object* v_idx_679_; lean_object* v_struct_680_; lean_object* v___x_681_; 
v_idx_679_ = lean_ctor_get(v_e_668_, 1);
lean_inc(v_idx_679_);
v_struct_680_ = lean_ctor_get(v_e_668_, 2);
lean_inc(v_struct_680_);
lean_dec_ref_known(v_e_668_, 3);
v___x_681_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_680_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_686_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v_a_682_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Nat_reprFast(v_idx_679_);
v___x_689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_687_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_690_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_dec(v_idx_679_);
return v___x_681_;
}
}
case 3:
{
lean_object* v_declName_695_; lean_object* v_us_696_; lean_object* v_args_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_declName_695_ = lean_ctor_get(v_e_668_, 0);
lean_inc(v_declName_695_);
v_us_696_ = lean_ctor_get(v_e_668_, 1);
lean_inc(v_us_696_);
v_args_697_ = lean_ctor_get(v_e_668_, 2);
lean_inc_ref(v_args_697_);
lean_dec_ref_known(v_e_668_, 3);
v___x_698_ = l_Lean_Expr_const___override(v_declName_695_, v_us_696_);
v___x_699_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_698_, v_a_669_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_697_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_697_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_700_);
lean_ctor_set(v___x_706_, 1, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
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
lean_dec(v_a_700_);
return v___x_701_;
}
}
else
{
lean_dec_ref(v_args_697_);
return v___x_699_;
}
}
case 4:
{
lean_object* v_fvarId_711_; lean_object* v_args_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_730_; 
v_fvarId_711_ = lean_ctor_get(v_e_668_, 0);
v_args_712_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_730_ == 0)
{
v___x_714_ = v_e_668_;
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_args_712_);
lean_inc(v_fvarId_711_);
lean_dec(v_e_668_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_711_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_712_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_712_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_729_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_729_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 5);
lean_ctor_set(v___x_714_, 1, v_a_719_);
lean_ctor_set(v___x_714_, 0, v_a_717_);
v___x_724_ = v___x_714_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_717_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_719_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_dec(v_a_717_);
lean_del_object(v___x_714_);
return v___x_718_;
}
}
else
{
lean_del_object(v___x_714_);
lean_dec_ref(v_args_712_);
return v___x_716_;
}
}
}
case 5:
{
lean_object* v_i_731_; lean_object* v_args_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_749_; 
v_i_731_ = lean_ctor_get(v_e_668_, 0);
v_args_732_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_749_ == 0)
{
v___x_734_ = v_e_668_;
v_isShared_735_ = v_isSharedCheck_749_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_args_732_);
lean_inc(v_i_731_);
lean_dec(v_e_668_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_749_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_732_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_732_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_737_);
lean_ctor_set(v___x_734_, 0, v___x_741_);
v___x_743_ = v___x_734_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_a_737_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
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
lean_del_object(v___x_734_);
lean_dec_ref(v_i_731_);
return v___x_736_;
}
}
}
case 6:
{
lean_object* v_i_750_; lean_object* v_var_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_773_; 
v_i_750_ = lean_ctor_get(v_e_668_, 0);
v_var_751_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_773_ == 0)
{
v___x_753_ = v_e_668_;
v_isShared_754_ = v_isSharedCheck_773_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_var_751_);
lean_inc(v_i_750_);
lean_dec(v_e_668_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_773_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_751_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_772_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_772_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_772_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_772_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_760_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_761_ = l_Nat_reprFast(v_i_750_);
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 5);
lean_ctor_set(v___x_753_, 1, v___x_762_);
lean_ctor_set(v___x_753_, 0, v___x_760_);
v___x_764_ = v___x_753_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_771_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_765_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_767_);
v___x_769_ = v___x_758_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_del_object(v___x_753_);
lean_dec(v_i_750_);
return v___x_755_;
}
}
}
case 7:
{
lean_object* v_i_774_; lean_object* v_var_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_797_; 
v_i_774_ = lean_ctor_get(v_e_668_, 0);
v_var_775_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_797_ == 0)
{
v___x_777_ = v_e_668_;
v_isShared_778_ = v_isSharedCheck_797_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_var_775_);
lean_inc(v_i_774_);
lean_dec(v_e_668_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_797_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_775_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_796_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_796_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_796_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_796_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_784_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
v___x_785_ = l_Nat_reprFast(v_i_774_);
v___x_786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 5);
lean_ctor_set(v___x_777_, 1, v___x_786_);
lean_ctor_set(v___x_777_, 0, v___x_784_);
v___x_788_ = v___x_777_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_795_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_789_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_791_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_del_object(v___x_777_);
lean_dec(v_i_774_);
return v___x_779_;
}
}
}
case 8:
{
lean_object* v_n_798_; lean_object* v_offset_799_; lean_object* v_var_800_; lean_object* v___x_801_; 
v_n_798_ = lean_ctor_get(v_e_668_, 0);
lean_inc(v_n_798_);
v_offset_799_ = lean_ctor_get(v_e_668_, 1);
lean_inc(v_offset_799_);
v_var_800_ = lean_ctor_get(v_e_668_, 2);
lean_inc(v_var_800_);
lean_dec_ref_known(v_e_668_, 3);
v___x_801_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_800_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_821_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_821_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_821_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_821_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_806_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_807_ = l_Nat_reprFast(v_n_798_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Nat_reprFast(v_offset_799_);
v___x_813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_817_);
v___x_819_ = v___x_804_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_dec(v_offset_799_);
lean_dec(v_n_798_);
return v___x_801_;
}
}
case 9:
{
lean_object* v_fn_822_; lean_object* v_args_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_842_; 
v_fn_822_ = lean_ctor_get(v_e_668_, 0);
v_args_823_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_842_ == 0)
{
v___x_825_ = v_e_668_;
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_args_823_);
lean_inc(v_fn_822_);
lean_dec(v_e_668_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_823_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_823_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_841_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_841_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_832_ = 1;
v___x_833_ = l_Lean_Name_toString(v_fn_822_, v___x_832_);
v___x_834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 5);
lean_ctor_set(v___x_825_, 1, v_a_828_);
lean_ctor_set(v___x_825_, 0, v___x_834_);
v___x_836_ = v___x_825_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_828_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_836_);
v___x_838_ = v___x_830_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
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
else
{
lean_del_object(v___x_825_);
lean_dec(v_fn_822_);
return v___x_827_;
}
}
}
case 10:
{
lean_object* v_fn_843_; lean_object* v_args_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_865_; 
v_fn_843_ = lean_ctor_get(v_e_668_, 0);
v_args_844_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_865_ == 0)
{
v___x_846_ = v_e_668_;
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_args_844_);
lean_inc(v_fn_843_);
lean_dec(v_e_668_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_844_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_844_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_864_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_864_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_864_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_864_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_853_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_854_ = 1;
v___x_855_ = l_Lean_Name_toString(v_fn_843_, v___x_854_);
v___x_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 5);
lean_ctor_set(v___x_846_, 1, v___x_856_);
lean_ctor_set(v___x_846_, 0, v___x_853_);
v___x_858_ = v___x_846_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_863_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_a_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_859_);
v___x_861_ = v___x_851_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_del_object(v___x_846_);
lean_dec(v_fn_843_);
return v___x_848_;
}
}
}
case 11:
{
lean_object* v_n_866_; lean_object* v_var_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_889_; 
v_n_866_ = lean_ctor_get(v_e_668_, 0);
v_var_867_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_889_ == 0)
{
v___x_869_ = v_e_668_;
v_isShared_870_ = v_isSharedCheck_889_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_var_867_);
lean_inc(v_n_866_);
lean_dec(v_e_668_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_889_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_867_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_888_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_876_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_877_ = l_Nat_reprFast(v_n_866_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 5);
lean_ctor_set(v___x_869_, 1, v___x_878_);
lean_ctor_set(v___x_869_, 0, v___x_876_);
v___x_880_ = v___x_869_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_887_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_881_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_883_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_del_object(v___x_869_);
lean_dec(v_n_866_);
return v___x_871_;
}
}
}
case 12:
{
lean_object* v_var_890_; lean_object* v_i_891_; uint8_t v_updateHeader_892_; lean_object* v_args_893_; lean_object* v___x_894_; 
v_var_890_ = lean_ctor_get(v_e_668_, 0);
lean_inc(v_var_890_);
v_i_891_ = lean_ctor_get(v_e_668_, 1);
lean_inc_ref(v_i_891_);
v_updateHeader_892_ = lean_ctor_get_uint8(v_e_668_, sizeof(void*)*3);
v_args_893_ = lean_ctor_get(v_e_668_, 2);
lean_inc_ref(v_args_893_);
lean_dec_ref_known(v_e_668_, 3);
v___x_894_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_890_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_667_, v_args_893_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_args_893_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_918_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_918_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___y_903_; 
v___x_901_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_892_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_903_ = v___x_916_;
goto v___jp_902_;
}
else
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_903_ = v___x_917_;
goto v___jp_902_;
}
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_inc(v___y_903_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___y_903_);
v___x_905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v_a_895_);
v___x_907_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_891_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_a_897_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_904_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_912_);
v___x_914_ = v___x_899_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_dec(v_a_895_);
lean_dec_ref(v_i_891_);
return v___x_896_;
}
}
else
{
lean_dec_ref(v_args_893_);
lean_dec_ref(v_i_891_);
return v___x_894_;
}
}
case 13:
{
lean_object* v_fvarId_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_936_; 
v_fvarId_919_ = lean_ctor_get(v_e_668_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_e_668_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_e_668_, 0);
lean_dec(v_unused_937_);
v___x_921_ = v_e_668_;
v_isShared_922_ = v_isSharedCheck_936_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_fvarId_919_);
lean_dec(v_e_668_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_936_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_919_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_935_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_935_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 5);
lean_ctor_set(v___x_921_, 1, v_a_924_);
lean_ctor_set(v___x_921_, 0, v___x_928_);
v___x_930_ = v___x_921_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_a_924_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_930_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_del_object(v___x_921_);
return v___x_923_;
}
}
}
case 14:
{
lean_object* v_fvarId_938_; lean_object* v___x_939_; 
v_fvarId_938_ = lean_ctor_get(v_e_668_, 0);
lean_inc(v_fvarId_938_);
lean_dec_ref_known(v_e_668_, 1);
v___x_939_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_938_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_949_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
return v___x_939_;
}
}
default: 
{
lean_object* v_fvarId_950_; lean_object* v___x_951_; 
v_fvarId_950_ = lean_ctor_get(v_e_668_, 0);
lean_inc(v_fvarId_950_);
lean_dec_ref_known(v_e_668_, 1);
v___x_951_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_950_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_961_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_956_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_962_, lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
uint8_t v_pu_boxed_970_; lean_object* v_res_971_; 
v_pu_boxed_970_ = lean_unbox(v_pu_962_);
v_res_971_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_970_, v_e_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_binderName_981_; lean_object* v_type_982_; uint8_t v_borrow_983_; lean_object* v___y_985_; 
v_binderName_981_ = lean_ctor_get(v_param_976_, 1);
lean_inc(v_binderName_981_);
v_type_982_ = lean_ctor_get(v_param_976_, 2);
lean_inc_ref(v_type_982_);
v_borrow_983_ = lean_ctor_get_uint8(v_param_976_, sizeof(void*)*3);
lean_dec_ref(v_param_976_);
if (v_borrow_983_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_985_ = v___x_1018_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_985_ = v___x_1019_;
goto v___jp_984_;
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_978_);
v___x_987_ = l_Lean_pp_funBinderTypes;
v___x_988_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_986_, v___x_987_);
lean_dec_ref(v___x_986_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v_type_982_);
v___x_989_ = 1;
v___x_990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_981_, v___x_989_);
lean_inc_ref(v___y_985_);
v___x_991_ = lean_string_append(v___y_985_, v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_982_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1017_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_999_ = l_Lean_Name_toString(v_binderName_981_, v___x_988_);
v___x_1000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_inc_ref(v___y_985_);
v___x_1003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___y_985_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_995_);
v___x_1006_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1007_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1005_);
v___x_1009_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1006_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_1012_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1013_);
v___x_1015_ = v___x_997_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_dec(v_binderName_981_);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1026_, lean_object* v_param_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1027_, v_a_1028_, v_a_1031_, v_a_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1035_, lean_object* v_param_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_pu_boxed_1043_; lean_object* v_res_1044_; 
v_pu_boxed_1043_ = lean_unbox(v_pu_1035_);
v_res_1044_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1043_, v_param_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1045_, lean_object* v_params_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1053_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1054_ = lean_box(v_pu_1045_);
v___x_1055_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1055_, 0, v___x_1054_);
v___x_1056_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1053_, v_params_1046_, v___x_1055_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1057_, lean_object* v_params_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint8_t v_pu_boxed_1065_; lean_object* v_res_1066_; 
v_pu_boxed_1065_ = lean_unbox(v_pu_1057_);
v_res_1066_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1065_, v_params_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_params_1058_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1073_, lean_object* v_letDecl_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1078_);
v___x_1082_ = l_Lean_pp_letVarTypes;
v___x_1083_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1081_, v___x_1082_);
lean_dec_ref(v___x_1081_);
if (v___x_1083_ == 0)
{
lean_object* v_binderName_1084_; lean_object* v_value_1085_; lean_object* v___x_1086_; 
v_binderName_1084_ = lean_ctor_get(v_letDecl_1074_, 1);
lean_inc(v_binderName_1084_);
v_value_1085_ = lean_ctor_get(v_letDecl_1074_, 3);
lean_inc(v_value_1085_);
lean_dec_ref(v_letDecl_1074_);
v___x_1086_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1073_, v_value_1085_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1102_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1102_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1102_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1091_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1092_ = 1;
v___x_1093_ = l_Lean_Name_toString(v_binderName_1084_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1098_);
v___x_1100_ = v___x_1089_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_dec(v_binderName_1084_);
return v___x_1086_;
}
}
else
{
lean_object* v_binderName_1103_; lean_object* v_type_1104_; lean_object* v_value_1105_; lean_object* v___x_1106_; 
v_binderName_1103_ = lean_ctor_get(v_letDecl_1074_, 1);
lean_inc(v_binderName_1103_);
v_type_1104_ = lean_ctor_get(v_letDecl_1074_, 2);
lean_inc_ref(v_type_1104_);
v_value_1105_ = lean_ctor_get(v_letDecl_1074_, 3);
lean_inc(v_value_1105_);
lean_dec_ref(v_letDecl_1074_);
v___x_1106_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1104_, v_a_1075_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1132_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1132_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1132_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1073_, v_value_1105_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1131_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1131_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1131_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1117_ = l_Lean_Name_toString(v_binderName_1103_, v___x_1083_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 3);
lean_ctor_set(v___x_1109_, 0, v___x_1117_);
v___x_1119_ = v___x_1109_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1116_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_a_1107_);
v___x_1124_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v_a_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1126_);
v___x_1128_ = v___x_1114_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_del_object(v___x_1109_);
lean_dec(v_a_1107_);
lean_dec(v_binderName_1103_);
return v___x_1111_;
}
}
}
else
{
lean_dec(v_value_1105_);
lean_dec(v_binderName_1103_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* v_pu_1133_, lean_object* v_letDecl_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
uint8_t v_pu_boxed_1141_; lean_object* v_res_1142_; 
v_pu_boxed_1141_ = lean_unbox(v_pu_1133_);
v_res_1142_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_boxed_1141_, v_letDecl_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1146_ == 0)
{
return v_bs_1145_;
}
else
{
lean_object* v_v_1147_; lean_object* v_fvarId_1148_; lean_object* v___x_1149_; lean_object* v_bs_x27_1150_; lean_object* v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v_v_1147_ = lean_array_uget_borrowed(v_bs_1145_, v_i_1144_);
v_fvarId_1148_ = lean_ctor_get(v_v_1147_, 0);
lean_inc(v_fvarId_1148_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v_bs_x27_1150_ = lean_array_uset(v_bs_1145_, v_i_1144_, v___x_1149_);
v___x_1151_ = l_Lean_mkFVar(v_fvarId_1148_);
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_add(v_i_1144_, v___x_1152_);
v___x_1154_ = lean_array_uset(v_bs_x27_1150_, v_i_1144_, v___x_1151_);
v_i_1144_ = v___x_1153_;
v_bs_1145_ = v___x_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_bs_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1159_, v_i_boxed_1160_, v_bs_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1162_, lean_object* v_ps_1163_, lean_object* v_type_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = l_Lean_Expr_isErased(v_type_1164_);
if (v___x_1168_ == 0)
{
if (v_pu_1162_ == 0)
{
size_t v_sz_1169_; size_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_sz_1169_ = lean_array_size(v_ps_1163_);
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1169_, v___x_1170_, v_ps_1163_);
v___x_1172_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1164_, v___x_1171_, v_a_1165_, v_a_1166_);
lean_dec_ref(v___x_1171_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref(v_ps_1163_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_type_1164_);
return v___x_1173_;
}
}
else
{
lean_object* v___x_1174_; 
lean_dec_ref(v_ps_1163_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_type_1164_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1175_, lean_object* v_ps_1176_, lean_object* v_type_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
uint8_t v_pu_boxed_1181_; lean_object* v_res_1182_; 
v_pu_boxed_1181_ = lean_unbox(v_pu_1175_);
v_res_1182_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1181_, v_ps_1176_, v_type_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1207_, lean_object* v_alt_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
switch(lean_obj_tag(v_alt_1208_))
{
case 0:
{
lean_object* v_ctorName_1215_; lean_object* v_params_1216_; lean_object* v_code_1217_; lean_object* v___x_1218_; 
v_ctorName_1215_ = lean_ctor_get(v_alt_1208_, 0);
lean_inc(v_ctorName_1215_);
v_params_1216_ = lean_ctor_get(v_alt_1208_, 1);
lean_inc_ref(v_params_1216_);
v_code_1217_ = lean_ctor_get(v_alt_1208_, 2);
lean_inc_ref(v_code_1217_);
lean_dec_ref_known(v_alt_1208_, 3);
v___x_1218_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1207_, v_params_1216_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec_ref(v_params_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1244_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1244_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1244_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1207_, v_code_1217_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1243_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1243_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1243_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1228_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1229_ = 1;
v___x_1230_ = l_Lean_Name_toString(v_ctorName_1215_, v___x_1229_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 3);
lean_ctor_set(v___x_1221_, 0, v___x_1230_);
v___x_1232_ = v___x_1221_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1228_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_a_1219_);
v___x_1235_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = l_Std_Format_indentD(v_a_1224_);
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1238_);
v___x_1240_ = v___x_1226_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_del_object(v___x_1221_);
lean_dec(v_a_1219_);
lean_dec(v_ctorName_1215_);
return v___x_1223_;
}
}
}
else
{
lean_dec_ref(v_code_1217_);
lean_dec(v_ctorName_1215_);
return v___x_1218_;
}
}
case 1:
{
lean_object* v_info_1245_; lean_object* v_code_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1271_; 
v_info_1245_ = lean_ctor_get(v_alt_1208_, 0);
v_code_1246_ = lean_ctor_get(v_alt_1208_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_alt_1208_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1248_ = v_alt_1208_;
v_isShared_1249_ = v_isSharedCheck_1271_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_code_1246_);
lean_inc(v_info_1245_);
lean_dec(v_alt_1208_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1271_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1207_, v_code_1246_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1270_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1270_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1270_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_name_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v_name_1255_ = lean_ctor_get(v_info_1245_, 0);
lean_inc(v_name_1255_);
lean_dec_ref(v_info_1245_);
v___x_1256_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1257_ = 1;
v___x_1258_ = l_Lean_Name_toString(v_name_1255_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 5);
lean_ctor_set(v___x_1248_, 1, v___x_1259_);
lean_ctor_set(v___x_1248_, 0, v___x_1256_);
v___x_1261_ = v___x_1248_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1262_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = l_Std_Format_indentD(v_a_1251_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1265_);
v___x_1267_ = v___x_1253_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_del_object(v___x_1248_);
lean_dec_ref(v_info_1245_);
return v___x_1250_;
}
}
}
default: 
{
lean_object* v_code_1272_; lean_object* v___x_1273_; 
v_code_1272_ = lean_ctor_get(v_alt_1208_, 0);
lean_inc_ref(v_code_1272_);
lean_dec_ref_known(v_alt_1208_, 1);
v___x_1273_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1207_, v_code_1272_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1284_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1278_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1279_ = l_Std_Format_indentD(v_a_1274_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1280_);
v___x_1282_ = v___x_1276_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1285_, lean_object* v_alt_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
uint8_t v_pu_boxed_1293_; lean_object* v_res_1294_; 
v_pu_boxed_1293_ = lean_unbox(v_pu_1285_);
v_res_1294_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1293_, v_alt_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec_ref(v_a_1287_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1346_, lean_object* v_c_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
switch(lean_obj_tag(v_c_1347_))
{
case 0:
{
lean_object* v_decl_1354_; lean_object* v_k_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1377_; 
v_decl_1354_ = lean_ctor_get(v_c_1347_, 0);
v_k_1355_ = lean_ctor_get(v_c_1347_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1357_ = v_c_1347_;
v_isShared_1358_ = v_isSharedCheck_1377_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_k_1355_);
lean_inc(v_decl_1354_);
lean_dec(v_c_1347_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1377_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1346_, v_decl_1354_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1355_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1376_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 5);
lean_ctor_set(v___x_1357_, 1, v___x_1366_);
lean_ctor_set(v___x_1357_, 0, v_a_1360_);
v___x_1368_ = v___x_1357_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1360_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1369_ = lean_box(1);
v___x_1370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_a_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1371_);
v___x_1373_ = v___x_1364_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_dec(v_a_1360_);
lean_del_object(v___x_1357_);
return v___x_1361_;
}
}
else
{
lean_del_object(v___x_1357_);
lean_dec_ref(v_k_1355_);
return v___x_1359_;
}
}
}
case 1:
{
lean_object* v_decl_1378_; lean_object* v_k_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1403_; 
v_decl_1378_ = lean_ctor_get(v_c_1347_, 0);
v_k_1379_ = lean_ctor_get(v_c_1347_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1381_ = v_c_1347_;
v_isShared_1382_ = v_isSharedCheck_1403_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_k_1379_);
lean_inc(v_decl_1378_);
lean_dec(v_c_1347_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1403_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1346_, v_decl_1378_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1379_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1402_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1402_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1402_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 5);
lean_ctor_set(v___x_1381_, 1, v_a_1384_);
lean_ctor_set(v___x_1381_, 0, v___x_1390_);
v___x_1392_ = v___x_1381_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_a_1384_);
v___x_1392_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1393_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_box(1);
v___x_1396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_a_1386_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1397_);
v___x_1399_ = v___x_1388_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_dec(v_a_1384_);
lean_del_object(v___x_1381_);
return v___x_1385_;
}
}
else
{
lean_del_object(v___x_1381_);
lean_dec_ref(v_k_1379_);
return v___x_1383_;
}
}
}
case 2:
{
lean_object* v_decl_1404_; lean_object* v_k_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1429_; 
v_decl_1404_ = lean_ctor_get(v_c_1347_, 0);
v_k_1405_ = lean_ctor_get(v_c_1347_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1407_ = v_c_1347_;
v_isShared_1408_ = v_isSharedCheck_1429_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_k_1405_);
lean_inc(v_decl_1404_);
lean_dec(v_c_1347_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1429_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1346_, v_decl_1404_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1405_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1428_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 5);
lean_ctor_set(v___x_1407_, 1, v_a_1410_);
lean_ctor_set(v___x_1407_, 0, v___x_1416_);
v___x_1418_ = v___x_1407_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_a_1410_);
v___x_1418_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1419_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_box(1);
v___x_1422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v_a_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1423_);
v___x_1425_ = v___x_1414_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_dec(v_a_1410_);
lean_del_object(v___x_1407_);
return v___x_1411_;
}
}
else
{
lean_del_object(v___x_1407_);
lean_dec_ref(v_k_1405_);
return v___x_1409_;
}
}
}
case 3:
{
lean_object* v_fvarId_1430_; lean_object* v_args_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1451_; 
v_fvarId_1430_ = lean_ctor_get(v_c_1347_, 0);
v_args_1431_ = lean_ctor_get(v_c_1347_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1433_ = v_c_1347_;
v_isShared_1434_ = v_isSharedCheck_1451_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_args_1431_);
lean_inc(v_fvarId_1430_);
lean_dec(v_c_1347_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1451_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1430_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1346_, v_args_1431_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec_ref(v_args_1431_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1450_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1450_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1450_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 5);
lean_ctor_set(v___x_1433_, 1, v_a_1436_);
lean_ctor_set(v___x_1433_, 0, v___x_1442_);
v___x_1444_ = v___x_1433_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_a_1436_);
v___x_1444_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v_a_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1447_ = v___x_1440_;
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
lean_dec(v_a_1436_);
lean_del_object(v___x_1433_);
return v___x_1437_;
}
}
else
{
lean_del_object(v___x_1433_);
lean_dec_ref(v_args_1431_);
return v___x_1435_;
}
}
}
case 4:
{
lean_object* v_cases_1452_; lean_object* v_resultType_1453_; lean_object* v_discr_1454_; lean_object* v_alts_1455_; lean_object* v___x_1456_; 
v_cases_1452_ = lean_ctor_get(v_c_1347_, 0);
lean_inc_ref(v_cases_1452_);
lean_dec_ref_known(v_c_1347_, 1);
v_resultType_1453_ = lean_ctor_get(v_cases_1452_, 1);
lean_inc_ref(v_resultType_1453_);
v_discr_1454_ = lean_ctor_get(v_cases_1452_, 2);
lean_inc(v_discr_1454_);
v_alts_1455_ = lean_ctor_get(v_cases_1452_, 3);
lean_inc_ref(v_alts_1455_);
lean_dec_ref(v_cases_1452_);
v___x_1456_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1454_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1453_, v_a_1348_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = lean_box(1);
v___x_1461_ = lean_box(v_pu_1346_);
v___x_1462_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1462_, 0, v___x_1461_);
v___x_1463_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1460_, v_alts_1455_, v___x_1462_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec_ref(v_alts_1455_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1477_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1468_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_a_1457_);
v___x_1470_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_a_1459_);
v___x_1473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1473_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_dec(v_a_1459_);
lean_dec(v_a_1457_);
return v___x_1463_;
}
}
else
{
lean_dec(v_a_1457_);
lean_dec_ref(v_alts_1455_);
return v___x_1458_;
}
}
else
{
lean_dec_ref(v_alts_1455_);
lean_dec_ref(v_resultType_1453_);
return v___x_1456_;
}
}
case 5:
{
lean_object* v_fvarId_1478_; lean_object* v___x_1479_; 
v_fvarId_1478_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1478_);
lean_dec_ref_known(v_c_1347_, 1);
v___x_1479_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1478_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_a_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1485_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
return v___x_1479_;
}
}
case 6:
{
lean_object* v_type_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1512_; 
v_type_1490_ = lean_ctor_get(v_c_1347_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1492_ = v_c_1347_;
v_isShared_1493_ = v_isSharedCheck_1512_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_type_1490_);
lean_dec(v_c_1347_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1512_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1351_);
v___x_1495_ = l_Lean_pp_all;
v___x_1496_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1494_, v___x_1495_);
lean_dec_ref(v___x_1494_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_dec_ref(v_type_1490_);
v___x_1497_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1497_);
v___x_1499_ = v___x_1492_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
lean_object* v___x_1501_; 
lean_del_object(v___x_1492_);
v___x_1501_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1490_, v_a_1348_, v_a_1351_, v_a_1352_);
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
v___x_1506_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
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
}
}
case 7:
{
lean_object* v_fvarId_1513_; lean_object* v_i_1514_; lean_object* v_y_1515_; lean_object* v_k_1516_; lean_object* v___x_1517_; 
v_fvarId_1513_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1513_);
v_i_1514_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_i_1514_);
v_y_1515_ = lean_ctor_get(v_c_1347_, 2);
lean_inc(v_y_1515_);
v_k_1516_ = lean_ctor_get(v_c_1347_, 3);
lean_inc_ref(v_k_1516_);
lean_dec_ref_known(v_c_1347_, 4);
v___x_1517_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1513_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1515_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1550_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1550_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1550_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1516_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1549_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1549_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1549_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1529_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_a_1518_);
v___x_1531_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Nat_reprFast(v_i_1514_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 3);
lean_ctor_set(v___x_1522_, 0, v___x_1533_);
v___x_1535_ = v___x_1522_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1532_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_a_1520_);
v___x_1540_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_box(1);
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1544_);
v___x_1546_ = v___x_1527_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_del_object(v___x_1522_);
lean_dec(v_a_1520_);
lean_dec(v_a_1518_);
lean_dec(v_i_1514_);
return v___x_1524_;
}
}
}
else
{
lean_dec(v_a_1518_);
lean_dec_ref(v_k_1516_);
lean_dec(v_i_1514_);
return v___x_1519_;
}
}
else
{
lean_dec_ref(v_k_1516_);
lean_dec(v_y_1515_);
lean_dec(v_i_1514_);
return v___x_1517_;
}
}
case 8:
{
lean_object* v_fvarId_1551_; lean_object* v_i_1552_; lean_object* v_y_1553_; lean_object* v_k_1554_; lean_object* v___x_1555_; 
v_fvarId_1551_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1551_);
v_i_1552_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_i_1552_);
v_y_1553_ = lean_ctor_get(v_c_1347_, 2);
lean_inc(v_y_1553_);
v_k_1554_ = lean_ctor_get(v_c_1347_, 3);
lean_inc_ref(v_k_1554_);
lean_dec_ref_known(v_c_1347_, 4);
v___x_1555_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1551_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1553_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1588_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1588_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1588_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1554_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1587_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1587_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1587_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1567_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_a_1556_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Nat_reprFast(v_i_1552_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 3);
lean_ctor_set(v___x_1560_, 0, v___x_1571_);
v___x_1573_ = v___x_1560_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1570_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_a_1558_);
v___x_1578_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_box(1);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1582_);
v___x_1584_ = v___x_1565_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_del_object(v___x_1560_);
lean_dec(v_a_1558_);
lean_dec(v_a_1556_);
lean_dec(v_i_1552_);
return v___x_1562_;
}
}
}
else
{
lean_dec(v_a_1556_);
lean_dec_ref(v_k_1554_);
lean_dec(v_i_1552_);
return v___x_1557_;
}
}
else
{
lean_dec_ref(v_k_1554_);
lean_dec(v_y_1553_);
lean_dec(v_i_1552_);
return v___x_1555_;
}
}
case 9:
{
lean_object* v_fvarId_1589_; lean_object* v_i_1590_; lean_object* v_offset_1591_; lean_object* v_y_1592_; lean_object* v_ty_1593_; lean_object* v_k_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_fvarId_1589_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1589_);
v_i_1590_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_i_1590_);
v_offset_1591_ = lean_ctor_get(v_c_1347_, 2);
lean_inc(v_offset_1591_);
v_y_1592_ = lean_ctor_get(v_c_1347_, 3);
lean_inc(v_y_1592_);
v_ty_1593_ = lean_ctor_get(v_c_1347_, 4);
lean_inc_ref(v_ty_1593_);
v_k_1594_ = lean_ctor_get(v_c_1347_, 5);
lean_inc_ref(v_k_1594_);
lean_dec_ref_known(v_c_1347_, 6);
v___x_1595_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1351_);
v___x_1596_ = l_Lean_pp_letVarTypes;
v___x_1597_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_1595_, v___x_1596_);
lean_dec_ref(v___x_1595_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref(v_ty_1593_);
v___x_1598_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1589_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1642_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1642_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1642_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1592_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1641_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1641_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1641_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1594_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1640_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1640_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1640_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1613_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_a_1599_);
v___x_1615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Nat_reprFast(v_i_1590_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 3);
lean_ctor_set(v___x_1606_, 0, v___x_1617_);
v___x_1619_ = v___x_1606_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Nat_reprFast(v_offset_1591_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 3);
lean_ctor_set(v___x_1601_, 0, v___x_1623_);
v___x_1625_ = v___x_1601_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1622_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_a_1604_);
v___x_1630_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_box(1);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1634_);
v___x_1636_ = v___x_1611_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_del_object(v___x_1606_);
lean_dec(v_a_1604_);
lean_del_object(v___x_1601_);
lean_dec(v_a_1599_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1608_;
}
}
}
else
{
lean_del_object(v___x_1601_);
lean_dec(v_a_1599_);
lean_dec_ref(v_k_1594_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1603_;
}
}
}
else
{
lean_dec_ref(v_k_1594_);
lean_dec(v_y_1592_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1598_;
}
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1589_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1593_, v_a_1348_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1692_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1692_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1692_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1592_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1691_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1691_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1691_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1594_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1690_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1690_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1690_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1660_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_a_1644_);
v___x_1662_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Nat_reprFast(v_i_1590_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 3);
lean_ctor_set(v___x_1653_, 0, v___x_1664_);
v___x_1666_ = v___x_1653_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1663_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Nat_reprFast(v_offset_1591_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 3);
lean_ctor_set(v___x_1648_, 0, v___x_1670_);
v___x_1672_ = v___x_1648_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1669_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v_a_1646_);
v___x_1677_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_a_1651_);
v___x_1680_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_box(1);
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v_a_1656_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1684_);
v___x_1686_ = v___x_1658_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_del_object(v___x_1653_);
lean_dec(v_a_1651_);
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_a_1644_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1655_;
}
}
}
else
{
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_a_1644_);
lean_dec_ref(v_k_1594_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1650_;
}
}
}
else
{
lean_dec(v_a_1644_);
lean_dec_ref(v_k_1594_);
lean_dec(v_y_1592_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1645_;
}
}
else
{
lean_dec_ref(v_k_1594_);
lean_dec_ref(v_ty_1593_);
lean_dec(v_y_1592_);
lean_dec(v_offset_1591_);
lean_dec(v_i_1590_);
return v___x_1643_;
}
}
}
case 10:
{
lean_object* v_fvarId_1693_; lean_object* v_cidx_1694_; lean_object* v_k_1695_; lean_object* v___x_1696_; 
v_fvarId_1693_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1693_);
v_cidx_1694_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_cidx_1694_);
v_k_1695_ = lean_ctor_get(v_c_1347_, 2);
lean_inc_ref(v_k_1695_);
lean_dec_ref_known(v_c_1347_, 3);
v___x_1696_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1693_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1724_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1695_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1723_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1706_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v_a_1697_);
v___x_1708_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Nat_reprFast(v_cidx_1694_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 3);
lean_ctor_set(v___x_1699_, 0, v___x_1710_);
v___x_1712_ = v___x_1699_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1709_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_box(1);
v___x_1717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v_a_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1718_);
v___x_1720_ = v___x_1704_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_del_object(v___x_1699_);
lean_dec(v_a_1697_);
lean_dec(v_cidx_1694_);
return v___x_1701_;
}
}
}
else
{
lean_dec_ref(v_k_1695_);
lean_dec(v_cidx_1694_);
return v___x_1696_;
}
}
case 11:
{
lean_object* v_fvarId_1725_; lean_object* v_n_1726_; uint8_t v_check_1727_; uint8_t v_persistent_1728_; lean_object* v_k_1729_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1798_; 
v_fvarId_1725_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1725_);
v_n_1726_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_n_1726_);
v_check_1727_ = lean_ctor_get_uint8(v_c_1347_, sizeof(void*)*3);
v_persistent_1728_ = lean_ctor_get_uint8(v_c_1347_, sizeof(void*)*3 + 1);
v_k_1729_ = lean_ctor_get(v_c_1347_, 2);
lean_inc_ref(v_k_1729_);
lean_dec_ref_known(v_c_1347_, 3);
if (v_persistent_1728_ == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1798_ = v___x_1801_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___y_1798_ = v___x_1802_;
goto v___jp_1797_;
}
v___jp_1730_:
{
lean_object* v_ann_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
lean_inc_ref(v___y_1731_);
v_ann_1733_ = lean_string_append(v___y_1731_, v___y_1732_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_dec_eq(v_n_1726_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1725_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1768_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1768_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1768_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1729_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1767_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1767_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1767_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1747_ = l_Nat_reprFast(v_n_1726_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 3);
lean_ctor_set(v___x_1739_, 0, v___x_1747_);
v___x_1749_ = v___x_1739_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1746_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_ann_1733_);
v___x_1754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_a_1737_);
v___x_1758_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_box(1);
v___x_1761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v_a_1742_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1762_);
v___x_1764_ = v___x_1744_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_del_object(v___x_1739_);
lean_dec(v_a_1737_);
lean_dec_ref(v_ann_1733_);
lean_dec(v_n_1726_);
return v___x_1741_;
}
}
}
else
{
lean_dec_ref(v_ann_1733_);
lean_dec_ref(v_k_1729_);
lean_dec(v_n_1726_);
return v___x_1736_;
}
}
else
{
lean_object* v___x_1769_; 
lean_dec(v_n_1726_);
v___x_1769_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1725_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1796_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1729_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1795_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1795_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1795_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 3);
lean_ctor_set(v___x_1772_, 0, v_ann_1733_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_ann_1733_);
v___x_1781_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v_a_1770_);
v___x_1786_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_box(1);
v___x_1789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1790_);
v___x_1792_ = v___x_1777_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_del_object(v___x_1772_);
lean_dec(v_a_1770_);
lean_dec_ref(v_ann_1733_);
return v___x_1774_;
}
}
}
else
{
lean_dec_ref(v_ann_1733_);
lean_dec_ref(v_k_1729_);
return v___x_1769_;
}
}
}
v___jp_1797_:
{
if (v_check_1727_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
v___y_1731_ = v___y_1798_;
v___y_1732_ = v___x_1799_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1731_ = v___y_1798_;
v___y_1732_ = v___x_1800_;
goto v___jp_1730_;
}
}
}
case 12:
{
lean_object* v_fvarId_1803_; lean_object* v_n_1804_; uint8_t v_check_1805_; uint8_t v_persistent_1806_; lean_object* v_objs_x3f_1807_; lean_object* v_k_1808_; lean_object* v_ann_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v_ann_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_ann_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; 
v_fvarId_1803_ = lean_ctor_get(v_c_1347_, 0);
lean_inc(v_fvarId_1803_);
v_n_1804_ = lean_ctor_get(v_c_1347_, 1);
lean_inc(v_n_1804_);
v_check_1805_ = lean_ctor_get_uint8(v_c_1347_, sizeof(void*)*4);
v_persistent_1806_ = lean_ctor_get_uint8(v_c_1347_, sizeof(void*)*4 + 1);
v_objs_x3f_1807_ = lean_ctor_get(v_c_1347_, 2);
lean_inc(v_objs_x3f_1807_);
v_k_1808_ = lean_ctor_get(v_c_1347_, 3);
lean_inc_ref(v_k_1808_);
lean_dec_ref_known(v_c_1347_, 4);
if (v_persistent_1806_ == 0)
{
lean_object* v_ann_1902_; 
v_ann_1902_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v_ann_1894_ = v_ann_1902_;
v___y_1895_ = v_a_1348_;
v___y_1896_ = v_a_1349_;
v___y_1897_ = v_a_1350_;
v___y_1898_ = v_a_1351_;
v___y_1899_ = v_a_1352_;
goto v___jp_1893_;
}
else
{
lean_object* v_ann_1903_; 
v_ann_1903_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v_ann_1894_ = v_ann_1903_;
v___y_1895_ = v_a_1348_;
v___y_1896_ = v_a_1349_;
v___y_1897_ = v_a_1350_;
v___y_1898_ = v_a_1351_;
v___y_1899_ = v_a_1352_;
goto v___jp_1893_;
}
v___jp_1809_:
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_dec_eq(v_n_1804_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1803_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1850_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1850_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1850_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1808_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1849_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1849_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1849_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1829_ = l_Nat_reprFast(v_n_1804_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 3);
lean_ctor_set(v___x_1821_, 0, v___x_1829_);
v___x_1831_ = v___x_1821_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1828_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_ann_1810_);
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v_a_1819_);
v___x_1840_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_box(1);
v___x_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_a_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1844_);
v___x_1846_ = v___x_1826_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_del_object(v___x_1821_);
lean_dec(v_a_1819_);
lean_dec_ref(v_ann_1810_);
lean_dec(v_n_1804_);
return v___x_1823_;
}
}
}
else
{
lean_dec_ref(v_ann_1810_);
lean_dec_ref(v_k_1808_);
lean_dec(v_n_1804_);
return v___x_1818_;
}
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_n_1804_);
v___x_1851_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1803_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1878_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1878_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1878_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1808_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1877_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1877_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1877_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 3);
lean_ctor_set(v___x_1854_, 0, v_ann_1810_);
v___x_1863_ = v___x_1854_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_ann_1810_);
v___x_1863_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1861_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v_a_1852_);
v___x_1868_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_box(1);
v___x_1871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1872_);
v___x_1874_ = v___x_1859_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_del_object(v___x_1854_);
lean_dec(v_a_1852_);
lean_dec_ref(v_ann_1810_);
return v___x_1856_;
}
}
}
else
{
lean_dec_ref(v_ann_1810_);
lean_dec_ref(v_k_1808_);
return v___x_1851_;
}
}
}
v___jp_1879_:
{
if (lean_obj_tag(v_objs_x3f_1807_) == 1)
{
lean_object* v_val_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_ann_1892_; 
v_val_1886_ = lean_ctor_get(v_objs_x3f_1807_, 0);
lean_inc(v_val_1886_);
lean_dec_ref_known(v_objs_x3f_1807_, 1);
v___x_1887_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0));
v___x_1888_ = l_Nat_reprFast(v_val_1886_);
v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__40));
v___x_1891_ = lean_string_append(v___x_1889_, v___x_1890_);
v_ann_1892_ = lean_string_append(v_ann_1880_, v___x_1891_);
lean_dec_ref(v___x_1891_);
v_ann_1810_ = v_ann_1892_;
v___y_1811_ = v___y_1881_;
v___y_1812_ = v___y_1882_;
v___y_1813_ = v___y_1883_;
v___y_1814_ = v___y_1884_;
v___y_1815_ = v___y_1885_;
goto v___jp_1809_;
}
else
{
lean_dec(v_objs_x3f_1807_);
v_ann_1810_ = v_ann_1880_;
v___y_1811_ = v___y_1881_;
v___y_1812_ = v___y_1882_;
v___y_1813_ = v___y_1883_;
v___y_1814_ = v___y_1884_;
v___y_1815_ = v___y_1885_;
goto v___jp_1809_;
}
}
v___jp_1893_:
{
if (v_check_1805_ == 0)
{
lean_object* v___x_1900_; lean_object* v_ann_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
lean_inc_ref(v_ann_1894_);
v_ann_1901_ = lean_string_append(v_ann_1894_, v___x_1900_);
v_ann_1880_ = v_ann_1901_;
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___y_1896_;
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___y_1898_;
v___y_1885_ = v___y_1899_;
goto v___jp_1879_;
}
else
{
lean_inc_ref(v_ann_1894_);
v_ann_1880_ = v_ann_1894_;
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___y_1896_;
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___y_1898_;
v___y_1885_ = v___y_1899_;
goto v___jp_1879_;
}
}
}
default: 
{
lean_object* v_fvarId_1904_; lean_object* v_k_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1929_; 
v_fvarId_1904_ = lean_ctor_get(v_c_1347_, 0);
v_k_1905_ = lean_ctor_get(v_c_1347_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_c_1347_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1907_ = v_c_1347_;
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_k_1905_);
lean_inc(v_fvarId_1904_);
lean_dec(v_c_1347_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1904_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1346_, v_k_1905_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1928_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1928_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1928_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__42));
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 5);
lean_ctor_set(v___x_1907_, 1, v_a_1910_);
lean_ctor_set(v___x_1907_, 0, v___x_1916_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1910_);
v___x_1918_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1919_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_box(1);
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_a_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1923_);
v___x_1925_ = v___x_1914_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_dec(v_a_1910_);
lean_del_object(v___x_1907_);
return v___x_1911_;
}
}
else
{
lean_del_object(v___x_1907_);
lean_dec_ref(v_k_1905_);
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1930_, lean_object* v_funDecl_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_binderName_1938_; lean_object* v_params_1939_; lean_object* v_type_1940_; lean_object* v_value_1941_; lean_object* v___x_1942_; 
v_binderName_1938_ = lean_ctor_get(v_funDecl_1931_, 1);
lean_inc(v_binderName_1938_);
v_params_1939_ = lean_ctor_get(v_funDecl_1931_, 2);
lean_inc_ref(v_params_1939_);
v_type_1940_ = lean_ctor_get(v_funDecl_1931_, 3);
lean_inc_ref(v_type_1940_);
v_value_1941_ = lean_ctor_get(v_funDecl_1931_, 4);
lean_inc_ref(v_value_1941_);
lean_dec_ref(v_funDecl_1931_);
v___x_1942_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1930_, v_params_1939_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1930_, v_params_1939_, v_type_1940_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1945_, v_a_1932_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1973_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1973_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1973_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1930_, v_value_1941_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1972_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1972_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1972_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1956_ = 1;
v___x_1957_ = l_Lean_Name_toString(v_binderName_1938_, v___x_1956_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 3);
lean_ctor_set(v___x_1949_, 0, v___x_1957_);
v___x_1959_ = v___x_1949_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v_a_1943_);
v___x_1961_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_a_1947_);
v___x_1964_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Std_Format_indentD(v_a_1952_);
v___x_1967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1967_);
v___x_1969_ = v___x_1954_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_del_object(v___x_1949_);
lean_dec(v_a_1947_);
lean_dec(v_a_1943_);
lean_dec(v_binderName_1938_);
return v___x_1951_;
}
}
}
else
{
lean_dec(v_a_1943_);
lean_dec_ref(v_value_1941_);
lean_dec(v_binderName_1938_);
return v___x_1946_;
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v_a_1943_);
lean_dec_ref(v_value_1941_);
lean_dec(v_binderName_1938_);
v_a_1974_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1944_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1944_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_dec_ref(v_value_1941_);
lean_dec_ref(v_type_1940_);
lean_dec_ref(v_params_1939_);
lean_dec(v_binderName_1938_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_1982_, lean_object* v_funDecl_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
uint8_t v_pu_boxed_1990_; lean_object* v_res_1991_; 
v_pu_boxed_1990_ = lean_unbox(v_pu_1982_);
v_res_1991_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_1990_, v_funDecl_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_1992_, lean_object* v_c_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
uint8_t v_pu_boxed_2000_; lean_object* v_res_2001_; 
v_pu_boxed_2000_ = lean_unbox(v_pu_1992_);
v_res_2001_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_2000_, v_c_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec_ref(v_a_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_2005_, lean_object* v_b_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
if (lean_obj_tag(v_b_2006_) == 0)
{
lean_object* v_code_2013_; lean_object* v___x_2014_; 
v_code_2013_ = lean_ctor_get(v_b_2006_, 0);
lean_inc_ref(v_code_2013_);
lean_dec_ref_known(v_b_2006_, 1);
v___x_2014_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_2005_, v_code_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
return v___x_2014_;
}
else
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
v_isSharedCheck_2022_ = !lean_is_exclusive(v_b_2006_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_b_2006_, 0);
lean_dec(v_unused_2023_);
v___x_2016_ = v_b_2006_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v_b_2006_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_2024_, lean_object* v_b_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
uint8_t v_pu_boxed_2032_; lean_object* v_res_2033_; 
v_pu_boxed_2032_ = lean_unbox(v_pu_2024_);
v_res_2033_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_2032_, v_b_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec_ref(v_a_2026_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_2034_, lean_object* v_opt_2035_){
_start:
{
lean_object* v_name_2036_; lean_object* v_defValue_2037_; lean_object* v_map_2038_; lean_object* v___x_2039_; 
v_name_2036_ = lean_ctor_get(v_opt_2035_, 0);
v_defValue_2037_ = lean_ctor_get(v_opt_2035_, 1);
v_map_2038_ = lean_ctor_get(v_opts_2034_, 0);
v___x_2039_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2038_, v_name_2036_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_inc(v_defValue_2037_);
return v_defValue_2037_;
}
else
{
lean_object* v_val_2040_; 
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_val_2040_) == 3)
{
lean_object* v_v_2041_; 
v_v_2041_ = lean_ctor_get(v_val_2040_, 0);
lean_inc(v_v_2041_);
lean_dec_ref_known(v_val_2040_, 1);
return v_v_2041_;
}
else
{
lean_dec(v_val_2040_);
lean_inc(v_defValue_2037_);
return v_defValue_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_2042_, lean_object* v_opt_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_2042_, v_opt_2043_);
lean_dec_ref(v_opt_2043_);
lean_dec_ref(v_opts_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(lean_object* v_o_2048_, lean_object* v_k_2049_, uint8_t v_v_2050_){
_start:
{
lean_object* v_map_2051_; uint8_t v_hasTrace_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2066_; 
v_map_2051_ = lean_ctor_get(v_o_2048_, 0);
v_hasTrace_2052_ = lean_ctor_get_uint8(v_o_2048_, sizeof(void*)*1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_o_2048_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2054_ = v_o_2048_;
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_map_2051_);
lean_dec(v_o_2048_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2056_, 0, v_v_2050_);
lean_inc(v_k_2049_);
v___x_2057_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2049_, v___x_2056_, v_map_2051_);
if (v_hasTrace_2052_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2061_; 
v___x_2058_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___closed__1));
v___x_2059_ = l_Lean_Name_isPrefixOf(v___x_2058_, v_k_2049_);
lean_dec(v_k_2049_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2057_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2057_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*1, v___x_2059_);
return v___x_2061_;
}
}
else
{
lean_object* v___x_2064_; 
lean_dec(v_k_2049_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2057_);
v___x_2064_ = v___x_2054_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*1, v_hasTrace_2052_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1___boxed(lean_object* v_o_2067_, lean_object* v_k_2068_, lean_object* v_v_2069_){
_start:
{
uint8_t v_v_boxed_2070_; lean_object* v_res_2071_; 
v_v_boxed_2070_ = lean_unbox(v_v_2069_);
v_res_2071_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_o_2067_, v_k_2068_, v_v_boxed_2070_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_2072_, lean_object* v_opt_2073_, uint8_t v_val_2074_){
_start:
{
lean_object* v_name_2075_; lean_object* v___x_2076_; 
v_name_2075_ = lean_ctor_get(v_opt_2073_, 0);
lean_inc(v_name_2075_);
lean_dec_ref(v_opt_2073_);
v___x_2076_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1_spec__1(v_opts_2072_, v_name_2075_, v_val_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_2077_, lean_object* v_opt_2078_, lean_object* v_val_2079_){
_start:
{
uint8_t v_val_boxed_2080_; lean_object* v_res_2081_; 
v_val_boxed_2080_ = lean_unbox(v_val_2079_);
v_res_2081_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2077_, v_opt_2078_, v_val_boxed_2080_);
return v_res_2081_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___y_2093_; uint16_t v___y_2094_; lean_object* v_fileName_2095_; lean_object* v_fileMap_2096_; lean_object* v_currNamespace_2097_; lean_object* v_openDecls_2098_; lean_object* v_initHeartbeats_2099_; lean_object* v_maxHeartbeats_2100_; lean_object* v_quotContext_2101_; lean_object* v_currMacroScope_2102_; lean_object* v_cancelTk_x3f_2103_; lean_object* v_inheritedTraceOptions_2104_; lean_object* v_currRecDepth_2105_; lean_object* v_ref_2106_; uint8_t v_suppressElabErrors_2107_; uint8_t v_isRecordingDeps_2108_; lean_object* v___y_2109_; lean_object* v_toCold_2129_; lean_object* v_currRecDepth_2130_; lean_object* v_ref_2131_; uint8_t v_suppressElabErrors_2132_; uint8_t v_isRecordingDeps_2133_; lean_object* v_fileName_2134_; lean_object* v_fileMap_2135_; lean_object* v_options_2136_; lean_object* v_currNamespace_2137_; lean_object* v_openDecls_2138_; lean_object* v_initHeartbeats_2139_; lean_object* v_maxHeartbeats_2140_; lean_object* v_quotContext_2141_; lean_object* v_currMacroScope_2142_; lean_object* v_cancelTk_x3f_2143_; lean_object* v_inheritedTraceOptions_2144_; lean_object* v___y_2146_; uint8_t v___y_2147_; uint16_t v___y_2148_; lean_object* v___y_2171_; 
v_toCold_2129_ = lean_ctor_get(v_a_2089_, 0);
v_currRecDepth_2130_ = lean_ctor_get(v_a_2089_, 1);
v_ref_2131_ = lean_ctor_get(v_a_2089_, 2);
v_suppressElabErrors_2132_ = lean_ctor_get_uint8(v_a_2089_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2133_ = lean_ctor_get_uint8(v_a_2089_, sizeof(void*)*3 + 3);
v_fileName_2134_ = lean_ctor_get(v_toCold_2129_, 0);
v_fileMap_2135_ = lean_ctor_get(v_toCold_2129_, 1);
v_options_2136_ = lean_ctor_get(v_toCold_2129_, 2);
v_currNamespace_2137_ = lean_ctor_get(v_toCold_2129_, 4);
v_openDecls_2138_ = lean_ctor_get(v_toCold_2129_, 5);
v_initHeartbeats_2139_ = lean_ctor_get(v_toCold_2129_, 6);
v_maxHeartbeats_2140_ = lean_ctor_get(v_toCold_2129_, 7);
v_quotContext_2141_ = lean_ctor_get(v_toCold_2129_, 8);
v_currMacroScope_2142_ = lean_ctor_get(v_toCold_2129_, 9);
v_cancelTk_x3f_2143_ = lean_ctor_get(v_toCold_2129_, 10);
v_inheritedTraceOptions_2144_ = lean_ctor_get(v_toCold_2129_, 11);
if (v_isRecordingDeps_2133_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = l_Lean_pp_sanitizeNames;
lean_inc_ref(v_options_2136_);
v___x_2183_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_options_2136_, v___x_2182_, v_isRecordingDeps_2133_);
v___y_2171_ = v___x_2183_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2184_; 
lean_inc_ref(v_options_2136_);
v___x_2184_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2136_);
v___y_2171_ = v___x_2184_;
goto v___jp_2170_;
}
v___jp_2092_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2110_ = l_Lean_maxRecDepth;
v___x_2111_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__0(v___y_2093_, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2112_, 0, v_fileName_2095_);
lean_ctor_set(v___x_2112_, 1, v_fileMap_2096_);
lean_ctor_set(v___x_2112_, 2, v___y_2093_);
lean_ctor_set(v___x_2112_, 3, v___x_2111_);
lean_ctor_set(v___x_2112_, 4, v_currNamespace_2097_);
lean_ctor_set(v___x_2112_, 5, v_openDecls_2098_);
lean_ctor_set(v___x_2112_, 6, v_initHeartbeats_2099_);
lean_ctor_set(v___x_2112_, 7, v_maxHeartbeats_2100_);
lean_ctor_set(v___x_2112_, 8, v_quotContext_2101_);
lean_ctor_set(v___x_2112_, 9, v_currMacroScope_2102_);
lean_ctor_set(v___x_2112_, 10, v_cancelTk_x3f_2103_);
lean_ctor_set(v___x_2112_, 11, v_inheritedTraceOptions_2104_);
lean_inc(v_ref_2106_);
lean_inc(v_currRecDepth_2105_);
v___x_2113_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_currRecDepth_2105_);
lean_ctor_set(v___x_2113_, 2, v_ref_2106_);
lean_ctor_set_uint16(v___x_2113_, sizeof(void*)*3, v___y_2094_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*3 + 2, v_suppressElabErrors_2107_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*3 + 3, v_isRecordingDeps_2108_);
v___x_2114_ = lean_st_ref_get(v_a_2088_);
v___x_2115_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2087_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v_lctx_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v_lctx_2117_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_lctx_2117_);
lean_dec(v___x_2114_);
v___x_2118_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
v___x_2119_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2117_, v___x_2118_);
lean_dec_ref(v_lctx_2117_);
lean_inc(v___y_2109_);
lean_inc(v_a_2088_);
lean_inc_ref(v_a_2087_);
v___x_2120_ = lean_apply_6(v_x_2086_, v___x_2119_, v_a_2087_, v_a_2088_, v___x_2113_, v___y_2109_, lean_box(0));
return v___x_2120_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v___x_2114_);
lean_dec_ref_known(v___x_2113_, 3);
lean_dec_ref(v_x_2086_);
v_a_2121_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2115_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2115_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
v___jp_2145_:
{
lean_object* v___x_2149_; lean_object* v_env_2150_; lean_object* v_nextMacroScope_2151_; lean_object* v_ngen_2152_; lean_object* v_auxDeclNGen_2153_; lean_object* v_traceState_2154_; lean_object* v_recordedDeps_2155_; lean_object* v_messages_2156_; lean_object* v_infoState_2157_; lean_object* v_snapshotTasks_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2168_; 
v___x_2149_ = lean_st_ref_take(v_a_2090_);
v_env_2150_ = lean_ctor_get(v___x_2149_, 0);
v_nextMacroScope_2151_ = lean_ctor_get(v___x_2149_, 1);
v_ngen_2152_ = lean_ctor_get(v___x_2149_, 2);
v_auxDeclNGen_2153_ = lean_ctor_get(v___x_2149_, 3);
v_traceState_2154_ = lean_ctor_get(v___x_2149_, 4);
v_recordedDeps_2155_ = lean_ctor_get(v___x_2149_, 6);
v_messages_2156_ = lean_ctor_get(v___x_2149_, 7);
v_infoState_2157_ = lean_ctor_get(v___x_2149_, 8);
v_snapshotTasks_2158_ = lean_ctor_get(v___x_2149_, 9);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2149_, 5);
lean_dec(v_unused_2169_);
v___x_2160_ = v___x_2149_;
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_snapshotTasks_2158_);
lean_inc(v_infoState_2157_);
lean_inc(v_messages_2156_);
lean_inc(v_recordedDeps_2155_);
lean_inc(v_traceState_2154_);
lean_inc(v_auxDeclNGen_2153_);
lean_inc(v_ngen_2152_);
lean_inc(v_nextMacroScope_2151_);
lean_inc(v_env_2150_);
lean_dec(v___x_2149_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2162_ = l_Lean_Kernel_enableDiag(v_env_2150_, v___y_2147_);
v___x_2163_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 5, v___x_2163_);
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2165_ = v___x_2160_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_nextMacroScope_2151_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_ngen_2152_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_auxDeclNGen_2153_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_traceState_2154_);
lean_ctor_set(v_reuseFailAlloc_2167_, 5, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2167_, 6, v_recordedDeps_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 7, v_messages_2156_);
lean_ctor_set(v_reuseFailAlloc_2167_, 8, v_infoState_2157_);
lean_ctor_set(v_reuseFailAlloc_2167_, 9, v_snapshotTasks_2158_);
v___x_2165_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_st_ref_put(v_a_2090_, v___x_2165_);
lean_inc_ref(v_inheritedTraceOptions_2144_);
lean_inc(v_cancelTk_x3f_2143_);
lean_inc(v_currMacroScope_2142_);
lean_inc(v_quotContext_2141_);
lean_inc(v_maxHeartbeats_2140_);
lean_inc(v_initHeartbeats_2139_);
lean_inc(v_openDecls_2138_);
lean_inc(v_currNamespace_2137_);
lean_inc_ref(v_fileMap_2135_);
lean_inc_ref(v_fileName_2134_);
v___y_2093_ = v___y_2146_;
v___y_2094_ = v___y_2148_;
v_fileName_2095_ = v_fileName_2134_;
v_fileMap_2096_ = v_fileMap_2135_;
v_currNamespace_2097_ = v_currNamespace_2137_;
v_openDecls_2098_ = v_openDecls_2138_;
v_initHeartbeats_2099_ = v_initHeartbeats_2139_;
v_maxHeartbeats_2100_ = v_maxHeartbeats_2140_;
v_quotContext_2101_ = v_quotContext_2141_;
v_currMacroScope_2102_ = v_currMacroScope_2142_;
v_cancelTk_x3f_2103_ = v_cancelTk_x3f_2143_;
v_inheritedTraceOptions_2104_ = v_inheritedTraceOptions_2144_;
v_currRecDepth_2105_ = v_currRecDepth_2130_;
v_ref_2106_ = v_ref_2131_;
v_suppressElabErrors_2107_ = v_suppressElabErrors_2132_;
v_isRecordingDeps_2108_ = v_isRecordingDeps_2133_;
v___y_2109_ = v_a_2090_;
goto v___jp_2092_;
}
}
}
v___jp_2170_:
{
uint16_t v___x_2172_; lean_object* v___x_2173_; lean_object* v_env_2174_; uint8_t v___x_2175_; uint16_t v___x_2176_; uint16_t v___x_2177_; uint16_t v___x_2178_; uint8_t v___x_2179_; 
v___x_2172_ = l_Lean_OptionFlags_ofOptions(v___y_2171_);
v___x_2173_ = lean_st_ref_get(v_a_2090_);
v_env_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc_ref(v_env_2174_);
lean_dec(v___x_2173_);
v___x_2175_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2174_);
lean_dec_ref(v_env_2174_);
v___x_2176_ = 512;
v___x_2177_ = lean_uint16_land(v___x_2172_, v___x_2176_);
v___x_2178_ = 0;
v___x_2179_ = lean_uint16_dec_eq(v___x_2177_, v___x_2178_);
if (v___x_2179_ == 0)
{
if (v___x_2175_ == 0)
{
uint8_t v___x_2180_; 
v___x_2180_ = 1;
v___y_2146_ = v___y_2171_;
v___y_2147_ = v___x_2180_;
v___y_2148_ = v___x_2172_;
goto v___jp_2145_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2144_);
lean_inc(v_cancelTk_x3f_2143_);
lean_inc(v_currMacroScope_2142_);
lean_inc(v_quotContext_2141_);
lean_inc(v_maxHeartbeats_2140_);
lean_inc(v_initHeartbeats_2139_);
lean_inc(v_openDecls_2138_);
lean_inc(v_currNamespace_2137_);
lean_inc_ref(v_fileMap_2135_);
lean_inc_ref(v_fileName_2134_);
v___y_2093_ = v___y_2171_;
v___y_2094_ = v___x_2172_;
v_fileName_2095_ = v_fileName_2134_;
v_fileMap_2096_ = v_fileMap_2135_;
v_currNamespace_2097_ = v_currNamespace_2137_;
v_openDecls_2098_ = v_openDecls_2138_;
v_initHeartbeats_2099_ = v_initHeartbeats_2139_;
v_maxHeartbeats_2100_ = v_maxHeartbeats_2140_;
v_quotContext_2101_ = v_quotContext_2141_;
v_currMacroScope_2102_ = v_currMacroScope_2142_;
v_cancelTk_x3f_2103_ = v_cancelTk_x3f_2143_;
v_inheritedTraceOptions_2104_ = v_inheritedTraceOptions_2144_;
v_currRecDepth_2105_ = v_currRecDepth_2130_;
v_ref_2106_ = v_ref_2131_;
v_suppressElabErrors_2107_ = v_suppressElabErrors_2132_;
v_isRecordingDeps_2108_ = v_isRecordingDeps_2133_;
v___y_2109_ = v_a_2090_;
goto v___jp_2092_;
}
}
else
{
if (v___x_2175_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2144_);
lean_inc(v_cancelTk_x3f_2143_);
lean_inc(v_currMacroScope_2142_);
lean_inc(v_quotContext_2141_);
lean_inc(v_maxHeartbeats_2140_);
lean_inc(v_initHeartbeats_2139_);
lean_inc(v_openDecls_2138_);
lean_inc(v_currNamespace_2137_);
lean_inc_ref(v_fileMap_2135_);
lean_inc_ref(v_fileName_2134_);
v___y_2093_ = v___y_2171_;
v___y_2094_ = v___x_2172_;
v_fileName_2095_ = v_fileName_2134_;
v_fileMap_2096_ = v_fileMap_2135_;
v_currNamespace_2097_ = v_currNamespace_2137_;
v_openDecls_2098_ = v_openDecls_2138_;
v_initHeartbeats_2099_ = v_initHeartbeats_2139_;
v_maxHeartbeats_2100_ = v_maxHeartbeats_2140_;
v_quotContext_2101_ = v_quotContext_2141_;
v_currMacroScope_2102_ = v_currMacroScope_2142_;
v_cancelTk_x3f_2103_ = v_cancelTk_x3f_2143_;
v_inheritedTraceOptions_2104_ = v_inheritedTraceOptions_2144_;
v_currRecDepth_2105_ = v_currRecDepth_2130_;
v_ref_2106_ = v_ref_2131_;
v_suppressElabErrors_2107_ = v_suppressElabErrors_2132_;
v_isRecordingDeps_2108_ = v_isRecordingDeps_2133_;
v___y_2109_ = v_a_2090_;
goto v___jp_2092_;
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = 0;
v___y_2146_ = v___y_2171_;
v___y_2147_ = v___x_2181_;
v___y_2148_ = v___x_2172_;
goto v___jp_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2192_, lean_object* v_x_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_x_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2200_, v_x_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2208_, lean_object* v_code_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_box(v_pu_2208_);
v___x_2216_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2216_, 0, v___x_2215_);
lean_closure_set(v___x_2216_, 1, v_code_2209_);
v___x_2217_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2216_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2218_, lean_object* v_code_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
uint8_t v_pu_boxed_2225_; lean_object* v_res_2226_; 
v_pu_boxed_2225_ = lean_unbox(v_pu_2218_);
v_res_2226_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2225_, v_code_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2227_, lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(v_pu_2227_);
v___x_2235_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2235_, 0, v___x_2234_);
lean_closure_set(v___x_2235_, 1, v_e_2228_);
v___x_2236_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2235_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2237_, lean_object* v_e_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
uint8_t v_pu_boxed_2244_; lean_object* v_res_2245_; 
v_pu_boxed_2244_ = lean_unbox(v_pu_2237_);
v_res_2245_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2244_, v_e_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2249_, lean_object* v_params_2250_, lean_object* v_type_2251_, lean_object* v_value_2252_, lean_object* v_name_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2249_, v_params_2250_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2249_, v_params_2250_, v_type_2251_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2263_, v___y_2254_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2293_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2293_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2293_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2249_, v_value_2252_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2292_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2292_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2292_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2274_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2275_ = 1;
v___x_2276_ = l_Lean_Name_toString(v_name_2253_, v___x_2275_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 3);
lean_ctor_set(v___x_2267_, 0, v___x_2276_);
v___x_2278_ = v___x_2267_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2274_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_a_2261_);
v___x_2281_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v_a_2265_);
v___x_2284_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = l_Std_Format_indentD(v_a_2270_);
v___x_2287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2287_);
v___x_2289_ = v___x_2272_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_del_object(v___x_2267_);
lean_dec(v_a_2265_);
lean_dec(v_a_2261_);
lean_dec(v_name_2253_);
return v___x_2269_;
}
}
}
else
{
lean_dec(v_a_2261_);
lean_dec(v_name_2253_);
lean_dec_ref(v_value_2252_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_a_2261_);
lean_dec(v_name_2253_);
lean_dec_ref(v_value_2252_);
v_a_2294_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2262_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2262_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_dec(v_name_2253_);
lean_dec_ref(v_value_2252_);
lean_dec_ref(v_type_2251_);
lean_dec_ref(v_params_2250_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2302_, lean_object* v_params_2303_, lean_object* v_type_2304_, lean_object* v_value_2305_, lean_object* v_name_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v_pu_boxed_2313_; lean_object* v_res_2314_; 
v_pu_boxed_2313_ = lean_unbox(v_pu_2302_);
v_res_2314_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2313_, v_params_2303_, v_type_2304_, v_value_2305_, v_name_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2315_, lean_object* v_decl_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_toSignature_2322_; lean_object* v_value_2323_; lean_object* v_name_2324_; lean_object* v_type_2325_; lean_object* v_params_2326_; lean_object* v___x_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; 
v_toSignature_2322_ = lean_ctor_get(v_decl_2316_, 0);
lean_inc_ref(v_toSignature_2322_);
v_value_2323_ = lean_ctor_get(v_decl_2316_, 1);
lean_inc_ref(v_value_2323_);
lean_dec_ref(v_decl_2316_);
v_name_2324_ = lean_ctor_get(v_toSignature_2322_, 0);
lean_inc(v_name_2324_);
v_type_2325_ = lean_ctor_get(v_toSignature_2322_, 2);
lean_inc_ref(v_type_2325_);
v_params_2326_ = lean_ctor_get(v_toSignature_2322_, 3);
lean_inc_ref(v_params_2326_);
lean_dec_ref(v_toSignature_2322_);
v___x_2327_ = lean_box(v_pu_2315_);
v___f_2328_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2328_, 0, v___x_2327_);
lean_closure_set(v___f_2328_, 1, v_params_2326_);
lean_closure_set(v___f_2328_, 2, v_type_2325_);
lean_closure_set(v___f_2328_, 3, v_value_2323_);
lean_closure_set(v___f_2328_, 4, v_name_2324_);
v___x_2329_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2328_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2330_, lean_object* v_decl_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v_pu_boxed_2337_; lean_object* v_res_2338_; 
v_pu_boxed_2337_ = lean_unbox(v_pu_2330_);
v_res_2338_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2337_, v_decl_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2339_, lean_object* v_decl_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2339_, v_decl_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2357_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v_a_2348_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2353_);
v___x_2355_ = v___x_2350_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2358_, lean_object* v_decl_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
uint8_t v_pu_boxed_2366_; lean_object* v_res_2367_; 
v_pu_boxed_2366_ = lean_unbox(v_pu_2358_);
v_res_2367_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2366_, v_decl_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2368_, lean_object* v_decl_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_box(v_pu_2368_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2376_, 0, v___x_2375_);
lean_closure_set(v___f_2376_, 1, v_decl_2369_);
v___x_2377_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2376_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2378_, lean_object* v_decl_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
uint8_t v_pu_boxed_2385_; lean_object* v_res_2386_; 
v_pu_boxed_2385_ = lean_unbox(v_pu_2378_);
v_res_2386_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2385_, v_decl_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2387_, lean_object* v_val_2388_, lean_object* v_a_x3f_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_st_ref_swap(v_a_2387_, v_val_2388_);
lean_dec(v___x_2392_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2394_, lean_object* v_val_2395_, lean_object* v_a_x3f_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2394_, v_val_2395_, v_a_x3f_2396_);
lean_dec(v_a_x3f_2396_);
lean_dec(v_a_2394_);
return v_res_2398_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_unsigned_to_nat(16u);
v___x_2401_ = lean_mk_array(v___x_2400_, v___x_2399_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2406_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
lean_ctor_set(v___x_2406_, 2, v___x_2405_);
lean_ctor_set(v___x_2406_, 3, v___x_2405_);
lean_ctor_set(v___x_2406_, 4, v___x_2405_);
lean_ctor_set(v___x_2406_, 5, v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2410_, lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_r_2417_; 
v___x_2415_ = lean_st_ref_get(v_a_2413_);
v___x_2416_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2417_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2411_, v___x_2416_, v_phase_2410_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v_r_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2434_; 
v_a_2418_ = lean_ctor_get(v_r_2417_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_r_2417_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2420_ = v_r_2417_;
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v_r_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
lean_inc(v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 1);
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v___x_2424_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2413_, v___x_2415_, v___x_2423_);
lean_dec_ref(v___x_2423_);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2432_);
v___x_2426_ = v___x_2424_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v___x_2424_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v_a_2418_);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2418_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_a_2435_ = lean_ctor_get(v_r_2417_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v_r_2417_, 1);
v___x_2436_ = lean_box(0);
v___x_2437_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2413_, v___x_2415_, v___x_2436_);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2445_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 1);
lean_ctor_set(v___x_2439_, 0, v_a_2435_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2435_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2446_, lean_object* v_x_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
uint8_t v_phase_boxed_2451_; lean_object* v_res_2452_; 
v_phase_boxed_2451_ = lean_unbox(v_phase_2446_);
v_res_2452_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2451_, v_x_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2453_, uint8_t v_phase_2454_, lean_object* v_x_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2454_, v_x_2455_, v_a_2456_, v_a_2457_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_phase_2461_, lean_object* v_x_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
uint8_t v_phase_boxed_2466_; lean_object* v_res_2467_; 
v_phase_boxed_2466_ = lean_unbox(v_phase_2461_);
v_res_2467_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2460_, v_phase_boxed_2466_, v_x_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2468_, lean_object* v_decl_2469_, lean_object* v___x_2470_, uint8_t v___x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2468_, v_decl_2469_, v___x_2470_, v___x_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v___x_2479_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2468_, v_a_2478_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2479_;
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2477_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2477_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2488_, lean_object* v_decl_2489_, lean_object* v___x_2490_, lean_object* v___x_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_pu_boxed_2497_; uint8_t v___x_100__boxed_2498_; lean_object* v_res_2499_; 
v_pu_boxed_2497_ = lean_unbox(v_pu_2488_);
v___x_100__boxed_2498_ = lean_unbox(v___x_2491_);
v_res_2499_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2497_, v_decl_2489_, v___x_2490_, v___x_100__boxed_2498_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2500_, lean_object* v_decl_2501_, uint8_t v_phase_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; 
v___x_2506_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2507_ = 0;
v___x_2508_ = lean_box(v_pu_2500_);
v___x_2509_ = lean_box(v___x_2507_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2510_, 0, v___x_2508_);
lean_closure_set(v___f_2510_, 1, v_decl_2501_);
lean_closure_set(v___f_2510_, 2, v___x_2506_);
lean_closure_set(v___f_2510_, 3, v___x_2509_);
v___x_2511_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2502_, v___f_2510_, v_a_2503_, v_a_2504_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2512_, lean_object* v_decl_2513_, lean_object* v_phase_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
uint8_t v_pu_boxed_2518_; uint8_t v_phase_boxed_2519_; lean_object* v_res_2520_; 
v_pu_boxed_2518_ = lean_unbox(v_pu_2512_);
v_phase_boxed_2519_ = lean_unbox(v_phase_2514_);
v_res_2520_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2518_, v_decl_2513_, v_phase_boxed_2519_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2521_, lean_object* v_code_2522_, lean_object* v___x_2523_, uint8_t v___x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2521_, v_code_2522_, v___x_2523_, v___x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2521_, v_a_2531_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2532_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_a_2533_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2530_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2530_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2541_, lean_object* v_code_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
uint8_t v_pu_boxed_2550_; uint8_t v___x_100__boxed_2551_; lean_object* v_res_2552_; 
v_pu_boxed_2550_ = lean_unbox(v_pu_2541_);
v___x_100__boxed_2551_ = lean_unbox(v___x_2544_);
v_res_2552_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2550_, v_code_2542_, v___x_2543_, v___x_100__boxed_2551_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2553_, lean_object* v_code_2554_, uint8_t v_phase_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; 
v___x_2559_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2560_ = 0;
v___x_2561_ = lean_box(v_pu_2553_);
v___x_2562_ = lean_box(v___x_2560_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2563_, 0, v___x_2561_);
lean_closure_set(v___f_2563_, 1, v_code_2554_);
lean_closure_set(v___f_2563_, 2, v___x_2559_);
lean_closure_set(v___f_2563_, 3, v___x_2562_);
v___x_2564_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2555_, v___f_2563_, v_a_2556_, v_a_2557_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2565_, lean_object* v_code_2566_, lean_object* v_phase_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
uint8_t v_pu_boxed_2571_; uint8_t v_phase_boxed_2572_; lean_object* v_res_2573_; 
v_pu_boxed_2571_ = lean_unbox(v_pu_2565_);
v_phase_boxed_2572_ = lean_unbox(v_phase_2567_);
v_res_2573_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2571_, v_code_2566_, v_phase_boxed_2572_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
return v_res_2573_;
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

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
extern lean_object* l_Lean_pp_funBinderTypes;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
extern lean_object* l_Lean_pp_sanitizeNames;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__2;
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
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_array_fget_borrowed(v_array_15_, v_start_16_);
lean_inc_ref(v_f_6_);
lean_inc(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___x_23_);
v___x_24_ = lean_apply_7(v_f_6_, v___x_23_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_24_, 1);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_start_16_, v___x_26_);
lean_dec(v_start_16_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_27_);
v___x_29_ = v___x_19_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_array_15_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v_stop_17_);
v___x_29_ = v_reuseFailAlloc_34_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_31_, 0, v_b_8_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_a_25_);
v_a_7_ = v___x_29_;
v_b_8_ = v___x_32_;
goto _start;
}
}
else
{
lean_del_object(v___x_19_);
lean_dec(v_stop_17_);
lean_dec(v_start_16_);
lean_dec_ref(v_array_15_);
lean_dec(v_b_8_);
lean_dec_ref(v_f_6_);
return v___x_24_;
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
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_269_; 
v_a_252_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_269_ == 0)
{
v___x_254_ = v___x_240_;
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_240_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___y_257_; uint8_t v___x_267_; 
v___x_267_ = l_Lean_Exception_isInterrupt(v_a_252_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
lean_inc(v_a_252_);
v___x_268_ = l_Lean_Exception_isRuntime(v_a_252_);
v___y_257_ = v___x_268_;
goto v___jp_256_;
}
else
{
v___y_257_ = v___x_267_;
goto v___jp_256_;
}
v___jp_256_:
{
if (v___y_257_ == 0)
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object* v_fvarId_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* v_fvarId_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_277_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* v_fvarId_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Compiler_LCNF_PP_ppFVar(v_fvarId_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_292_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_299_; uint64_t v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2(void){
_start:
{
uint64_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_uint64_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1);
v___x_302_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0));
v___x_303_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set_uint64(v___x_303_, sizeof(void*)*1, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_310_);
lean_ctor_set(v___x_311_, 4, v___x_309_);
lean_ctor_set(v___x_311_, 5, v___x_309_);
lean_ctor_set(v___x_311_, 6, v___x_309_);
lean_ctor_set(v___x_311_, 7, v___x_309_);
lean_ctor_set(v___x_311_, 8, v___x_309_);
lean_ctor_set(v___x_311_, 9, v___x_309_);
lean_ctor_set(v___x_311_, 10, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_313_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_ctor_set(v___x_313_, 3, v___x_312_);
lean_ctor_set(v___x_313_, 4, v___x_312_);
lean_ctor_set(v___x_313_, 5, v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_unsigned_to_nat(32u);
v___x_315_ = lean_mk_empty_array_with_capacity(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9(void){
_start:
{
size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = ((size_t)5ULL);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_unsigned_to_nat(32u);
v___x_320_ = lean_mk_empty_array_with_capacity(v___x_319_);
v___x_321_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
v___x_322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_318_);
lean_ctor_set(v___x_322_, 3, v___x_318_);
lean_ctor_set_usize(v___x_322_, 4, v___x_317_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
v___x_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v___x_323_);
lean_ctor_set(v___x_324_, 3, v___x_323_);
lean_ctor_set(v___x_324_, 4, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10);
v___x_326_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
v___x_327_ = lean_box(1);
v___x_328_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
v___x_329_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
v___x_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_327_);
lean_ctor_set(v___x_330_, 3, v___x_326_);
lean_ctor_set(v___x_330_, 4, v___x_325_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* v_e_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_336_ = lean_box(1);
v___x_337_ = 0;
v___x_338_ = 1;
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3));
v___x_342_ = lean_box(0);
lean_inc_ref(v_a_332_);
v___x_343_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_343_, 0, v___x_339_);
lean_ctor_set(v___x_343_, 1, v___x_336_);
lean_ctor_set(v___x_343_, 2, v_a_332_);
lean_ctor_set(v___x_343_, 3, v___x_341_);
lean_ctor_set(v___x_343_, 4, v___x_342_);
lean_ctor_set(v___x_343_, 5, v___x_340_);
lean_ctor_set(v___x_343_, 6, v___x_342_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*7, v___x_337_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*7 + 1, v___x_337_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*7 + 2, v___x_337_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*7 + 3, v___x_338_);
v___x_344_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11, &l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once, _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11);
v___x_345_ = lean_st_mk_ref(v___x_344_);
v___x_346_ = l_Lean_Meta_ppExpr(v_e_331_, v___x_343_, v___x_345_, v_a_333_, v_a_334_);
lean_dec_ref_known(v___x_343_, 7);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_st_ref_get(v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_351_);
if (v_isShared_350_ == 0)
{
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_347_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_dec(v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_362_, v_a_363_, v_a_366_, v_a_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* v_e_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Compiler_LCNF_PP_ppExpr(v_e_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* v_opts_378_, lean_object* v_opt_379_){
_start:
{
lean_object* v_name_380_; lean_object* v_defValue_381_; lean_object* v_map_382_; lean_object* v___x_383_; 
v_name_380_ = lean_ctor_get(v_opt_379_, 0);
v_defValue_381_ = lean_ctor_get(v_opt_379_, 1);
v_map_382_ = lean_ctor_get(v_opts_378_, 0);
v___x_383_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_382_, v_name_380_);
if (lean_obj_tag(v___x_383_) == 0)
{
uint8_t v___x_384_; 
v___x_384_ = lean_unbox(v_defValue_381_);
return v___x_384_;
}
else
{
lean_object* v_val_385_; 
v_val_385_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v___x_383_, 1);
if (lean_obj_tag(v_val_385_) == 1)
{
uint8_t v_v_386_; 
v_v_386_ = lean_ctor_get_uint8(v_val_385_, 0);
lean_dec_ref_known(v_val_385_, 0);
return v_v_386_;
}
else
{
uint8_t v___x_387_; 
lean_dec(v_val_385_);
v___x_387_ = lean_unbox(v_defValue_381_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* v_opts_388_, lean_object* v_opt_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_388_, v_opt_389_);
lean_dec_ref(v_opt_389_);
lean_dec_ref(v_opts_388_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_nat_to_int(v_a_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
v___x_403_ = lean_string_length(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
v___x_405_ = lean_nat_to_int(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
switch(lean_obj_tag(v_e_410_))
{
case 0:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
case 1:
{
lean_object* v_fvarId_419_; lean_object* v___x_420_; 
v_fvarId_419_ = lean_ctor_get(v_e_410_, 0);
lean_inc(v_fvarId_419_);
lean_dec_ref_known(v_e_410_, 1);
v___x_420_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_419_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
return v___x_420_;
}
default: 
{
lean_object* v_expr_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_457_; 
v_expr_421_ = lean_ctor_get(v_e_410_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_e_410_);
if (v_isSharedCheck_457_ == 0)
{
v___x_423_ = v_e_410_;
v_isShared_424_ = v_isSharedCheck_457_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_expr_421_);
lean_dec(v_e_410_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_457_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_options_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_options_425_ = lean_ctor_get(v_a_414_, 1);
v___x_426_ = l_Lean_pp_explicit;
v___x_427_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec_ref(v_expr_421_);
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 0);
lean_ctor_set(v___x_423_, 0, v___x_428_);
v___x_430_ = v___x_423_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
uint8_t v___x_432_; 
lean_del_object(v___x_423_);
v___x_432_ = l_Lean_Expr_isConst(v_expr_421_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_Expr_isProp(v_expr_421_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_Expr_isType0(v_expr_421_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_Expr_isFVar(v_expr_421_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_421_, v_a_411_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_452_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_452_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_452_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_452_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_441_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_442_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v_a_437_);
v___x_444_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_441_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = 0;
v___x_448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___x_447_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_448_);
v___x_450_ = v___x_439_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
return v___x_436_;
}
}
else
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_421_, v_a_411_, v_a_414_, v_a_415_);
return v___x_453_;
}
}
else
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_421_, v_a_411_, v_a_414_, v_a_415_);
return v___x_454_;
}
}
else
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_421_, v_a_411_, v_a_414_, v_a_415_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_expr_421_, v_a_411_, v_a_414_, v_a_415_);
return v___x_456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* v_e_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t v_pu_466_, lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* v_pu_475_, lean_object* v_e_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
uint8_t v_pu_boxed_483_; lean_object* v_res_484_; 
v_pu_boxed_483_ = lean_unbox(v_pu_475_);
v_res_484_ = l_Lean_Compiler_LCNF_PP_ppArg(v_pu_boxed_483_, v_e_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t v_pu_485_, lean_object* v_args_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_494_ = lean_box(v_pu_485_);
v___x_495_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(v___x_495_, 0, v___x_494_);
v___x_496_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_493_, v_args_486_, v___x_495_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* v_pu_497_, lean_object* v_args_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_pu_boxed_505_; lean_object* v_res_506_; 
v_pu_boxed_505_ = lean_unbox(v_pu_497_);
v_res_506_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_boxed_505_, v_args_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec_ref(v_args_498_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* v_lit_507_){
_start:
{
uint64_t v_v_510_; 
switch(lean_obj_tag(v_lit_507_))
{
case 0:
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v_val_515_ = lean_ctor_get(v_lit_507_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_lit_507_);
if (v_isSharedCheck_524_ == 0)
{
v___x_517_ = v_lit_507_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v_lit_507_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Nat_reprFast(v_val_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 3);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
case 1:
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_534_; 
v_val_525_ = lean_ctor_get(v_lit_507_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_lit_507_);
if (v_isSharedCheck_534_ == 0)
{
v___x_527_ = v_lit_507_;
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v_lit_507_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_String_quote(v_val_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 3);
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
case 2:
{
uint8_t v_val_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_val_535_ = lean_ctor_get_uint8(v_lit_507_, 0);
lean_dec_ref_known(v_lit_507_, 0);
v___x_536_ = lean_uint8_to_nat(v_val_535_);
v___x_537_ = l_Nat_reprFast(v___x_536_);
v___x_538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
case 3:
{
uint16_t v_val_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_val_540_ = lean_ctor_get_uint16(v_lit_507_, 0);
lean_dec_ref_known(v_lit_507_, 0);
v___x_541_ = lean_uint16_to_nat(v_val_540_);
v___x_542_ = l_Nat_reprFast(v___x_541_);
v___x_543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
case 4:
{
uint32_t v_val_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_val_545_ = lean_ctor_get_uint32(v_lit_507_, 0);
lean_dec_ref_known(v_lit_507_, 0);
v___x_546_ = lean_uint32_to_nat(v_val_545_);
v___x_547_ = l_Nat_reprFast(v___x_546_);
v___x_548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
default: 
{
uint64_t v_val_550_; 
v_val_550_ = lean_ctor_get_uint64(v_lit_507_, 0);
lean_dec_ref(v_lit_507_);
v_v_510_ = v_val_550_;
goto v___jp_509_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = lean_uint64_to_nat(v_v_510_);
v___x_512_ = l_Nat_reprFast(v___x_511_);
v___x_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* v_lit_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* v_lit_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_554_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* v_lit_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Compiler_LCNF_PP_ppLitValue(v_lit_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* v_x_582_){
_start:
{
lean_object* v_name_583_; lean_object* v_cidx_584_; lean_object* v_usize_585_; lean_object* v_ssize_586_; lean_object* v_r_588_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_r_602_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_name_583_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_name_583_);
v_cidx_584_ = lean_ctor_get(v_x_582_, 1);
lean_inc(v_cidx_584_);
v_usize_585_ = lean_ctor_get(v_x_582_, 3);
lean_inc(v_usize_585_);
v_ssize_586_ = lean_ctor_get(v_x_582_, 4);
lean_inc(v_ssize_586_);
lean_dec_ref(v_x_582_);
v___x_599_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
v___x_600_ = l_Nat_reprFast(v_cidx_584_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v_r_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_602_, 0, v___x_599_);
lean_ctor_set(v_r_602_, 1, v___x_601_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_lt(v___x_613_, v_usize_585_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v___x_613_, v_ssize_586_);
if (v___x_615_ == 0)
{
lean_dec(v_ssize_586_);
lean_dec(v_usize_585_);
v_r_588_ = v_r_602_;
goto v___jp_587_;
}
else
{
goto v___jp_603_;
}
}
else
{
goto v___jp_603_;
}
v___jp_587_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_box(0);
v___x_590_ = lean_name_eq(v_name_583_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_r_598_; 
v___x_591_ = 1;
v___x_592_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v_r_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_Name_toString(v_name_583_, v___x_591_);
v___x_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_593_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v_r_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_598_, 0, v___x_596_);
lean_ctor_set(v_r_598_, 1, v___x_597_);
return v_r_598_;
}
else
{
lean_dec(v_name_583_);
return v_r_588_;
}
}
v___jp_603_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_r_612_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v_r_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Nat_reprFast(v_usize_585_);
v___x_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_604_);
v___x_610_ = l_Nat_reprFast(v_ssize_586_);
v___x_611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
v_r_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_612_, 0, v___x_609_);
lean_ctor_set(v_r_612_, 1, v___x_611_);
v_r_588_ = v_r_612_;
goto v___jp_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_665_, lean_object* v_e_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
switch(lean_obj_tag(v_e_666_))
{
case 0:
{
lean_object* v_value_673_; lean_object* v___x_674_; 
v_value_673_ = lean_ctor_get(v_e_666_, 0);
lean_inc_ref(v_value_673_);
lean_dec_ref_known(v_e_666_, 1);
v___x_674_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_673_);
return v___x_674_;
}
case 1:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
case 2:
{
lean_object* v_idx_677_; lean_object* v_struct_678_; lean_object* v___x_679_; 
v_idx_677_ = lean_ctor_get(v_e_666_, 1);
lean_inc(v_idx_677_);
v_struct_678_ = lean_ctor_get(v_e_666_, 2);
lean_inc(v_struct_678_);
lean_dec_ref_known(v_e_666_, 3);
v___x_679_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_678_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_692_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_692_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_684_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_685_, 0, v_a_680_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Nat_reprFast(v_idx_677_);
v___x_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_685_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_688_);
v___x_690_ = v___x_682_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_dec(v_idx_677_);
return v___x_679_;
}
}
case 3:
{
lean_object* v_declName_693_; lean_object* v_us_694_; lean_object* v_args_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_declName_693_ = lean_ctor_get(v_e_666_, 0);
lean_inc(v_declName_693_);
v_us_694_ = lean_ctor_get(v_e_666_, 1);
lean_inc(v_us_694_);
v_args_695_ = lean_ctor_get(v_e_666_, 2);
lean_inc_ref(v_args_695_);
lean_dec_ref_known(v_e_666_, 3);
v___x_696_ = l_Lean_Expr_const___override(v_declName_693_, v_us_694_);
v___x_697_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_696_, v_a_667_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_695_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_695_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v_a_698_);
lean_ctor_set(v___x_704_, 1, v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_dec(v_a_698_);
return v___x_699_;
}
}
else
{
lean_dec_ref(v_args_695_);
return v___x_697_;
}
}
case 4:
{
lean_object* v_fvarId_709_; lean_object* v_args_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_728_; 
v_fvarId_709_ = lean_ctor_get(v_e_666_, 0);
v_args_710_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_728_ == 0)
{
v___x_712_ = v_e_666_;
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_args_710_);
lean_inc(v_fvarId_709_);
lean_dec(v_e_666_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_709_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_710_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_710_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_727_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_727_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 5);
lean_ctor_set(v___x_712_, 1, v_a_717_);
lean_ctor_set(v___x_712_, 0, v_a_715_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_a_717_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
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
}
else
{
lean_dec(v_a_715_);
lean_del_object(v___x_712_);
return v___x_716_;
}
}
else
{
lean_del_object(v___x_712_);
lean_dec_ref(v_args_710_);
return v___x_714_;
}
}
}
case 5:
{
lean_object* v_i_729_; lean_object* v_args_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_747_; 
v_i_729_ = lean_ctor_get(v_e_666_, 0);
v_args_730_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_747_ == 0)
{
v___x_732_ = v_e_666_;
v_isShared_733_ = v_isSharedCheck_747_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_args_730_);
lean_inc(v_i_729_);
lean_dec(v_e_666_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_747_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_730_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_746_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_746_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v_a_735_);
lean_ctor_set(v___x_732_, 0, v___x_739_);
v___x_741_ = v___x_732_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_735_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_741_);
v___x_743_ = v___x_737_;
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
lean_del_object(v___x_732_);
lean_dec_ref(v_i_729_);
return v___x_734_;
}
}
}
case 6:
{
lean_object* v_i_748_; lean_object* v_var_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_771_; 
v_i_748_ = lean_ctor_get(v_e_666_, 0);
v_var_749_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_771_ == 0)
{
v___x_751_ = v_e_666_;
v_isShared_752_ = v_isSharedCheck_771_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_var_749_);
lean_inc(v_i_748_);
lean_dec(v_e_666_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_771_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_749_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_770_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_770_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_770_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_770_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_758_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_759_ = l_Nat_reprFast(v_i_748_);
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 5);
lean_ctor_set(v___x_751_, 1, v___x_760_);
lean_ctor_set(v___x_751_, 0, v___x_758_);
v___x_762_ = v___x_751_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_769_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_765_);
v___x_767_ = v___x_756_;
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
lean_del_object(v___x_751_);
lean_dec(v_i_748_);
return v___x_753_;
}
}
}
case 7:
{
lean_object* v_i_772_; lean_object* v_var_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_795_; 
v_i_772_ = lean_ctor_get(v_e_666_, 0);
v_var_773_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_795_ == 0)
{
v___x_775_ = v_e_666_;
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_var_773_);
lean_inc(v_i_772_);
lean_dec(v_e_666_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_773_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
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
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
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
case 8:
{
lean_object* v_n_796_; lean_object* v_offset_797_; lean_object* v_var_798_; lean_object* v___x_799_; 
v_n_796_ = lean_ctor_get(v_e_666_, 0);
lean_inc(v_n_796_);
v_offset_797_ = lean_ctor_get(v_e_666_, 1);
lean_inc(v_offset_797_);
v_var_798_ = lean_ctor_get(v_e_666_, 2);
lean_inc(v_var_798_);
lean_dec_ref_known(v_e_666_, 3);
v___x_799_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_798_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_819_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_819_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_819_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_804_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_805_ = l_Nat_reprFast(v_n_796_);
v___x_806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Nat_reprFast(v_offset_797_);
v___x_811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_809_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_a_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_815_);
v___x_817_ = v___x_802_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_dec(v_offset_797_);
lean_dec(v_n_796_);
return v___x_799_;
}
}
case 9:
{
lean_object* v_fn_820_; lean_object* v_args_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_840_; 
v_fn_820_ = lean_ctor_get(v_e_666_, 0);
v_args_821_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_840_ == 0)
{
v___x_823_ = v_e_666_;
v_isShared_824_ = v_isSharedCheck_840_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_args_821_);
lean_inc(v_fn_820_);
lean_dec(v_e_666_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_840_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_821_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_821_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_839_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_839_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_830_ = 1;
v___x_831_ = l_Lean_Name_toString(v_fn_820_, v___x_830_);
v___x_832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 5);
lean_ctor_set(v___x_823_, 1, v_a_826_);
lean_ctor_set(v___x_823_, 0, v___x_832_);
v___x_834_ = v___x_823_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_826_);
v___x_834_ = v_reuseFailAlloc_838_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_836_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_834_);
v___x_836_ = v___x_828_;
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
}
else
{
lean_del_object(v___x_823_);
lean_dec(v_fn_820_);
return v___x_825_;
}
}
}
case 10:
{
lean_object* v_fn_841_; lean_object* v_args_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_863_; 
v_fn_841_ = lean_ctor_get(v_e_666_, 0);
v_args_842_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_863_ == 0)
{
v___x_844_ = v_e_666_;
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_args_842_);
lean_inc(v_fn_841_);
lean_dec(v_e_666_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_863_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_842_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_862_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_862_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_862_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_862_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_851_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_852_ = 1;
v___x_853_ = l_Lean_Name_toString(v_fn_841_, v___x_852_);
v___x_854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 5);
lean_ctor_set(v___x_844_, 1, v___x_854_);
lean_ctor_set(v___x_844_, 0, v___x_851_);
v___x_856_ = v___x_844_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_861_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v_a_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_857_);
v___x_859_ = v___x_849_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_del_object(v___x_844_);
lean_dec(v_fn_841_);
return v___x_846_;
}
}
}
case 11:
{
lean_object* v_n_864_; lean_object* v_var_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_887_; 
v_n_864_ = lean_ctor_get(v_e_666_, 0);
v_var_865_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_887_ == 0)
{
v___x_867_ = v_e_666_;
v_isShared_868_ = v_isSharedCheck_887_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_var_865_);
lean_inc(v_n_864_);
lean_dec(v_e_666_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_887_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_865_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_886_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_886_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_886_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_886_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_874_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_875_ = l_Nat_reprFast(v_n_864_);
v___x_876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 5);
lean_ctor_set(v___x_867_, 1, v___x_876_);
lean_ctor_set(v___x_867_, 0, v___x_874_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_885_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_879_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_881_);
v___x_883_ = v___x_872_;
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
lean_del_object(v___x_867_);
lean_dec(v_n_864_);
return v___x_869_;
}
}
}
case 12:
{
lean_object* v_var_888_; lean_object* v_i_889_; uint8_t v_updateHeader_890_; lean_object* v_args_891_; lean_object* v___x_892_; 
v_var_888_ = lean_ctor_get(v_e_666_, 0);
lean_inc(v_var_888_);
v_i_889_ = lean_ctor_get(v_e_666_, 1);
lean_inc_ref(v_i_889_);
v_updateHeader_890_ = lean_ctor_get_uint8(v_e_666_, sizeof(void*)*3);
v_args_891_ = lean_ctor_get(v_e_666_, 2);
lean_inc_ref(v_args_891_);
lean_dec_ref_known(v_e_666_, 3);
v___x_892_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_888_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_665_, v_args_891_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_args_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_916_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___y_901_; 
v___x_899_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_890_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_901_ = v___x_914_;
goto v___jp_900_;
}
else
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_901_ = v___x_915_;
goto v___jp_900_;
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
lean_inc(v___y_901_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___y_901_);
v___x_903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_a_893_);
v___x_905_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_889_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v_a_895_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_902_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_910_);
v___x_912_ = v___x_897_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_dec(v_a_893_);
lean_dec_ref(v_i_889_);
return v___x_894_;
}
}
else
{
lean_dec_ref(v_args_891_);
lean_dec_ref(v_i_889_);
return v___x_892_;
}
}
case 13:
{
lean_object* v_fvarId_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_934_; 
v_fvarId_917_ = lean_ctor_get(v_e_666_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_e_666_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_e_666_, 0);
lean_dec(v_unused_935_);
v___x_919_ = v_e_666_;
v_isShared_920_ = v_isSharedCheck_934_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_fvarId_917_);
lean_dec(v_e_666_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_934_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_917_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_933_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_933_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 5);
lean_ctor_set(v___x_919_, 1, v_a_922_);
lean_ctor_set(v___x_919_, 0, v___x_926_);
v___x_928_ = v___x_919_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_a_922_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_928_);
v___x_930_ = v___x_924_;
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
lean_del_object(v___x_919_);
return v___x_921_;
}
}
}
case 14:
{
lean_object* v_fvarId_936_; lean_object* v___x_937_; 
v_fvarId_936_ = lean_ctor_get(v_e_666_, 0);
lean_inc(v_fvarId_936_);
lean_dec_ref_known(v_e_666_, 1);
v___x_937_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_936_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_947_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_947_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_942_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_943_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
return v___x_937_;
}
}
default: 
{
lean_object* v_fvarId_948_; lean_object* v___x_949_; 
v_fvarId_948_ = lean_ctor_get(v_e_666_, 0);
lean_inc(v_fvarId_948_);
lean_dec_ref_known(v_e_666_, 1);
v___x_949_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_948_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
else
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_960_, lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
uint8_t v_pu_boxed_968_; lean_object* v_res_969_; 
v_pu_boxed_968_ = lean_unbox(v_pu_960_);
v_res_969_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_968_, v_e_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_a_962_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_binderName_979_; lean_object* v_type_980_; uint8_t v_borrow_981_; lean_object* v___y_983_; 
v_binderName_979_ = lean_ctor_get(v_param_974_, 1);
lean_inc(v_binderName_979_);
v_type_980_ = lean_ctor_get(v_param_974_, 2);
lean_inc_ref(v_type_980_);
v_borrow_981_ = lean_ctor_get_uint8(v_param_974_, sizeof(void*)*3);
lean_dec_ref(v_param_974_);
if (v_borrow_981_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_983_ = v___x_1016_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_983_ = v___x_1017_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v_options_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_options_984_ = lean_ctor_get(v_a_976_, 1);
v___x_985_ = l_Lean_pp_funBinderTypes;
v___x_986_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_984_, v___x_985_);
if (v___x_986_ == 0)
{
uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref(v_type_980_);
v___x_987_ = 1;
v___x_988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_979_, v___x_987_);
lean_inc_ref(v___y_983_);
v___x_989_ = lean_string_append(v___y_983_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_980_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1015_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1015_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1015_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_997_ = l_Lean_Name_toString(v_binderName_979_, v___x_986_);
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
lean_inc_ref(v___y_983_);
v___x_1001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___y_983_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v_a_993_);
v___x_1004_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1005_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1003_);
v___x_1007_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1004_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = 0;
v___x_1011_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*1, v___x_1010_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1011_);
v___x_1013_ = v___x_995_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_dec(v_binderName_979_);
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1024_, lean_object* v_param_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1025_, v_a_1026_, v_a_1029_, v_a_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1033_, lean_object* v_param_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
uint8_t v_pu_boxed_1041_; lean_object* v_res_1042_; 
v_pu_boxed_1041_ = lean_unbox(v_pu_1033_);
v_res_1042_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1041_, v_param_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec_ref(v_a_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1043_, lean_object* v_params_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1052_ = lean_box(v_pu_1043_);
v___x_1053_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1051_, v_params_1044_, v___x_1053_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1055_, lean_object* v_params_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
uint8_t v_pu_boxed_1063_; lean_object* v_res_1064_; 
v_pu_boxed_1063_ = lean_unbox(v_pu_1055_);
v_res_1064_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1063_, v_params_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec_ref(v_params_1056_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1071_, lean_object* v_letDecl_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_options_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_options_1079_ = lean_ctor_get(v_a_1076_, 1);
v___x_1080_ = l_Lean_pp_letVarTypes;
v___x_1081_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v_binderName_1082_; lean_object* v_value_1083_; lean_object* v___x_1084_; 
v_binderName_1082_ = lean_ctor_get(v_letDecl_1072_, 1);
lean_inc(v_binderName_1082_);
v_value_1083_ = lean_ctor_get(v_letDecl_1072_, 3);
lean_inc(v_value_1083_);
lean_dec_ref(v_letDecl_1072_);
v___x_1084_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1071_, v_value_1083_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1100_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1100_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1100_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1089_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1090_ = 1;
v___x_1091_ = l_Lean_Name_toString(v_binderName_1082_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1089_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1096_);
v___x_1098_ = v___x_1087_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_dec(v_binderName_1082_);
return v___x_1084_;
}
}
else
{
lean_object* v_binderName_1101_; lean_object* v_type_1102_; lean_object* v_value_1103_; lean_object* v___x_1104_; 
v_binderName_1101_ = lean_ctor_get(v_letDecl_1072_, 1);
lean_inc(v_binderName_1101_);
v_type_1102_ = lean_ctor_get(v_letDecl_1072_, 2);
lean_inc_ref(v_type_1102_);
v_value_1103_ = lean_ctor_get(v_letDecl_1072_, 3);
lean_inc(v_value_1103_);
lean_dec_ref(v_letDecl_1072_);
v___x_1104_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1102_, v_a_1073_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1130_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1130_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1130_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1071_, v_value_1103_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1129_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1115_ = l_Lean_Name_toString(v_binderName_1101_, v___x_1081_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 3);
lean_ctor_set(v___x_1107_, 0, v___x_1115_);
v___x_1117_ = v___x_1107_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1114_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v_a_1105_);
v___x_1122_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_a_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1124_);
v___x_1126_ = v___x_1112_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_del_object(v___x_1107_);
lean_dec(v_a_1105_);
lean_dec(v_binderName_1101_);
return v___x_1109_;
}
}
}
else
{
lean_dec(v_value_1103_);
lean_dec(v_binderName_1101_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* v_pu_1131_, lean_object* v_letDecl_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_pu_boxed_1139_; lean_object* v_res_1140_; 
v_pu_boxed_1139_ = lean_unbox(v_pu_1131_);
v_res_1140_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_boxed_1139_, v_letDecl_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_a_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_bs_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1144_ == 0)
{
return v_bs_1143_;
}
else
{
lean_object* v_v_1145_; lean_object* v_fvarId_1146_; lean_object* v___x_1147_; lean_object* v_bs_x27_1148_; lean_object* v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
v_v_1145_ = lean_array_uget_borrowed(v_bs_1143_, v_i_1142_);
v_fvarId_1146_ = lean_ctor_get(v_v_1145_, 0);
lean_inc(v_fvarId_1146_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v_bs_x27_1148_ = lean_array_uset(v_bs_1143_, v_i_1142_, v___x_1147_);
v___x_1149_ = l_Lean_mkFVar(v_fvarId_1146_);
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1142_, v___x_1150_);
v___x_1152_ = lean_array_uset(v_bs_x27_1148_, v_i_1142_, v___x_1149_);
v_i_1142_ = v___x_1151_;
v_bs_1143_ = v___x_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_bs_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1157_, v_i_boxed_1158_, v_bs_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1160_, lean_object* v_ps_1161_, lean_object* v_type_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Lean_Expr_isErased(v_type_1162_);
if (v___x_1166_ == 0)
{
if (v_pu_1160_ == 0)
{
size_t v_sz_1167_; size_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_sz_1167_ = lean_array_size(v_ps_1161_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1167_, v___x_1168_, v_ps_1161_);
v___x_1170_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1162_, v___x_1169_, v_a_1163_, v_a_1164_);
lean_dec_ref(v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_dec_ref(v_ps_1161_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_type_1162_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; 
lean_dec_ref(v_ps_1161_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_type_1162_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1173_, lean_object* v_ps_1174_, lean_object* v_type_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_pu_boxed_1179_; lean_object* v_res_1180_; 
v_pu_boxed_1179_ = lean_unbox(v_pu_1173_);
v_res_1180_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1179_, v_ps_1174_, v_type_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1205_, lean_object* v_alt_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
switch(lean_obj_tag(v_alt_1206_))
{
case 0:
{
lean_object* v_ctorName_1213_; lean_object* v_params_1214_; lean_object* v_code_1215_; lean_object* v___x_1216_; 
v_ctorName_1213_ = lean_ctor_get(v_alt_1206_, 0);
lean_inc(v_ctorName_1213_);
v_params_1214_ = lean_ctor_get(v_alt_1206_, 1);
lean_inc_ref(v_params_1214_);
v_code_1215_ = lean_ctor_get(v_alt_1206_, 2);
lean_inc_ref(v_code_1215_);
lean_dec_ref_known(v_alt_1206_, 3);
v___x_1216_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1205_, v_params_1214_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec_ref(v_params_1214_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1242_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1242_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1242_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1205_, v_code_1215_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1241_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1241_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1241_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1226_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1227_ = 1;
v___x_1228_ = l_Lean_Name_toString(v_ctorName_1213_, v___x_1227_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 3);
lean_ctor_set(v___x_1219_, 0, v___x_1228_);
v___x_1230_ = v___x_1219_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1226_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_a_1217_);
v___x_1233_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Std_Format_indentD(v_a_1222_);
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1236_);
v___x_1238_ = v___x_1224_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_del_object(v___x_1219_);
lean_dec(v_a_1217_);
lean_dec(v_ctorName_1213_);
return v___x_1221_;
}
}
}
else
{
lean_dec_ref(v_code_1215_);
lean_dec(v_ctorName_1213_);
return v___x_1216_;
}
}
case 1:
{
lean_object* v_info_1243_; lean_object* v_code_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1269_; 
v_info_1243_ = lean_ctor_get(v_alt_1206_, 0);
v_code_1244_ = lean_ctor_get(v_alt_1206_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_alt_1206_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1246_ = v_alt_1206_;
v_isShared_1247_ = v_isSharedCheck_1269_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_code_1244_);
lean_inc(v_info_1243_);
lean_dec(v_alt_1206_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1269_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1205_, v_code_1244_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1268_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_name_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_name_1253_ = lean_ctor_get(v_info_1243_, 0);
lean_inc(v_name_1253_);
lean_dec_ref(v_info_1243_);
v___x_1254_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1255_ = 1;
v___x_1256_ = l_Lean_Name_toString(v_name_1253_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 5);
lean_ctor_set(v___x_1246_, 1, v___x_1257_);
lean_ctor_set(v___x_1246_, 0, v___x_1254_);
v___x_1259_ = v___x_1246_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1260_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Std_Format_indentD(v_a_1249_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1263_);
v___x_1265_ = v___x_1251_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_del_object(v___x_1246_);
lean_dec_ref(v_info_1243_);
return v___x_1248_;
}
}
}
default: 
{
lean_object* v_code_1270_; lean_object* v___x_1271_; 
v_code_1270_ = lean_ctor_get(v_alt_1206_, 0);
lean_inc_ref(v_code_1270_);
lean_dec_ref_known(v_alt_1206_, 1);
v___x_1271_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1205_, v_code_1270_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1282_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1276_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1277_ = l_Std_Format_indentD(v_a_1272_);
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1278_);
v___x_1280_ = v___x_1274_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1283_, lean_object* v_alt_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v_pu_boxed_1291_; lean_object* v_res_1292_; 
v_pu_boxed_1291_ = lean_unbox(v_pu_1283_);
v_res_1292_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1291_, v_alt_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1344_, lean_object* v_c_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
switch(lean_obj_tag(v_c_1345_))
{
case 0:
{
lean_object* v_decl_1352_; lean_object* v_k_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1375_; 
v_decl_1352_ = lean_ctor_get(v_c_1345_, 0);
v_k_1353_ = lean_ctor_get(v_c_1345_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1355_ = v_c_1345_;
v_isShared_1356_ = v_isSharedCheck_1375_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_k_1353_);
lean_inc(v_decl_1352_);
lean_dec(v_c_1345_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1375_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1344_, v_decl_1352_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1353_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1374_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 5);
lean_ctor_set(v___x_1355_, 1, v___x_1364_);
lean_ctor_set(v___x_1355_, 0, v_a_1358_);
v___x_1366_ = v___x_1355_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1367_ = lean_box(1);
v___x_1368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v_a_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1369_);
v___x_1371_ = v___x_1362_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_dec(v_a_1358_);
lean_del_object(v___x_1355_);
return v___x_1359_;
}
}
else
{
lean_del_object(v___x_1355_);
lean_dec_ref(v_k_1353_);
return v___x_1357_;
}
}
}
case 1:
{
lean_object* v_decl_1376_; lean_object* v_k_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1401_; 
v_decl_1376_ = lean_ctor_get(v_c_1345_, 0);
v_k_1377_ = lean_ctor_get(v_c_1345_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1379_ = v_c_1345_;
v_isShared_1380_ = v_isSharedCheck_1401_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_k_1377_);
lean_inc(v_decl_1376_);
lean_dec(v_c_1345_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1401_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1344_, v_decl_1376_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1377_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1400_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1400_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1400_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 5);
lean_ctor_set(v___x_1379_, 1, v_a_1382_);
lean_ctor_set(v___x_1379_, 0, v___x_1388_);
v___x_1390_ = v___x_1379_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_a_1382_);
v___x_1390_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1391_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_box(1);
v___x_1394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1395_);
v___x_1397_ = v___x_1386_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
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
case 2:
{
lean_object* v_decl_1402_; lean_object* v_k_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1427_; 
v_decl_1402_ = lean_ctor_get(v_c_1345_, 0);
v_k_1403_ = lean_ctor_get(v_c_1345_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1405_ = v_c_1345_;
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_k_1403_);
lean_inc(v_decl_1402_);
lean_dec(v_c_1345_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1344_, v_decl_1402_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1403_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1426_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1426_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1426_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 5);
lean_ctor_set(v___x_1405_, 1, v_a_1408_);
lean_ctor_set(v___x_1405_, 0, v___x_1414_);
v___x_1416_ = v___x_1405_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_a_1408_);
v___x_1416_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1417_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_box(1);
v___x_1420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1421_);
v___x_1423_ = v___x_1412_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_dec(v_a_1408_);
lean_del_object(v___x_1405_);
return v___x_1409_;
}
}
else
{
lean_del_object(v___x_1405_);
lean_dec_ref(v_k_1403_);
return v___x_1407_;
}
}
}
case 3:
{
lean_object* v_fvarId_1428_; lean_object* v_args_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1449_; 
v_fvarId_1428_ = lean_ctor_get(v_c_1345_, 0);
v_args_1429_ = lean_ctor_get(v_c_1345_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1431_ = v_c_1345_;
v_isShared_1432_ = v_isSharedCheck_1449_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_args_1429_);
lean_inc(v_fvarId_1428_);
lean_dec(v_c_1345_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1449_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1428_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1344_, v_args_1429_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref(v_args_1429_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1448_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1448_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1448_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 5);
lean_ctor_set(v___x_1431_, 1, v_a_1434_);
lean_ctor_set(v___x_1431_, 0, v___x_1440_);
v___x_1442_ = v___x_1431_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_a_1434_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1443_);
v___x_1445_ = v___x_1438_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_dec(v_a_1434_);
lean_del_object(v___x_1431_);
return v___x_1435_;
}
}
else
{
lean_del_object(v___x_1431_);
lean_dec_ref(v_args_1429_);
return v___x_1433_;
}
}
}
case 4:
{
lean_object* v_cases_1450_; lean_object* v_resultType_1451_; lean_object* v_discr_1452_; lean_object* v_alts_1453_; lean_object* v___x_1454_; 
v_cases_1450_ = lean_ctor_get(v_c_1345_, 0);
lean_inc_ref(v_cases_1450_);
lean_dec_ref_known(v_c_1345_, 1);
v_resultType_1451_ = lean_ctor_get(v_cases_1450_, 1);
lean_inc_ref(v_resultType_1451_);
v_discr_1452_ = lean_ctor_get(v_cases_1450_, 2);
lean_inc(v_discr_1452_);
v_alts_1453_ = lean_ctor_get(v_cases_1450_, 3);
lean_inc_ref(v_alts_1453_);
lean_dec_ref(v_cases_1450_);
v___x_1454_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1452_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1451_, v_a_1346_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = lean_box(1);
v___x_1459_ = lean_box(v_pu_1344_);
v___x_1460_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1458_, v_alts_1453_, v___x_1460_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref(v_alts_1453_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1475_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1475_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1475_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1466_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_a_1455_);
v___x_1468_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_a_1457_);
v___x_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_a_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1471_);
v___x_1473_ = v___x_1464_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_dec(v_a_1457_);
lean_dec(v_a_1455_);
return v___x_1461_;
}
}
else
{
lean_dec(v_a_1455_);
lean_dec_ref(v_alts_1453_);
return v___x_1456_;
}
}
else
{
lean_dec_ref(v_alts_1453_);
lean_dec_ref(v_resultType_1451_);
return v___x_1454_;
}
}
case 5:
{
lean_object* v_fvarId_1476_; lean_object* v___x_1477_; 
v_fvarId_1476_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1476_);
lean_dec_ref_known(v_c_1345_, 1);
v___x_1477_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1476_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1487_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1482_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1483_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
return v___x_1477_;
}
}
case 6:
{
lean_object* v_type_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1510_; 
v_type_1488_ = lean_ctor_get(v_c_1345_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1490_ = v_c_1345_;
v_isShared_1491_ = v_isSharedCheck_1510_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_type_1488_);
lean_dec(v_c_1345_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1510_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_options_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_options_1492_ = lean_ctor_get(v_a_1349_, 1);
v___x_1493_ = l_Lean_pp_all;
v___x_1494_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec_ref(v_type_1488_);
v___x_1495_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1495_);
v___x_1497_ = v___x_1490_;
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
else
{
lean_object* v___x_1499_; 
lean_del_object(v___x_1490_);
v___x_1499_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1488_, v_a_1346_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1509_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
v___x_1505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
return v___x_1499_;
}
}
}
}
case 7:
{
lean_object* v_fvarId_1511_; lean_object* v_i_1512_; lean_object* v_y_1513_; lean_object* v_k_1514_; lean_object* v___x_1515_; 
v_fvarId_1511_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1511_);
v_i_1512_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_i_1512_);
v_y_1513_ = lean_ctor_get(v_c_1345_, 2);
lean_inc(v_y_1513_);
v_k_1514_ = lean_ctor_get(v_c_1345_, 3);
lean_inc_ref(v_k_1514_);
lean_dec_ref_known(v_c_1345_, 4);
v___x_1515_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1511_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1513_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1548_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1514_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1547_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1527_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v_a_1516_);
v___x_1529_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Nat_reprFast(v_i_1512_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 3);
lean_ctor_set(v___x_1520_, 0, v___x_1531_);
v___x_1533_ = v___x_1520_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1530_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v_a_1518_);
v___x_1538_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_box(1);
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1542_);
v___x_1544_ = v___x_1525_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_del_object(v___x_1520_);
lean_dec(v_a_1518_);
lean_dec(v_a_1516_);
lean_dec(v_i_1512_);
return v___x_1522_;
}
}
}
else
{
lean_dec(v_a_1516_);
lean_dec_ref(v_k_1514_);
lean_dec(v_i_1512_);
return v___x_1517_;
}
}
else
{
lean_dec_ref(v_k_1514_);
lean_dec(v_y_1513_);
lean_dec(v_i_1512_);
return v___x_1515_;
}
}
case 8:
{
lean_object* v_fvarId_1549_; lean_object* v_i_1550_; lean_object* v_y_1551_; lean_object* v_k_1552_; lean_object* v___x_1553_; 
v_fvarId_1549_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1549_);
v_i_1550_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_i_1550_);
v_y_1551_ = lean_ctor_get(v_c_1345_, 2);
lean_inc(v_y_1551_);
v_k_1552_ = lean_ctor_get(v_c_1345_, 3);
lean_inc_ref(v_k_1552_);
lean_dec_ref_known(v_c_1345_, 4);
v___x_1553_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1549_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1551_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1586_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1586_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1586_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1552_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1585_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1585_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1585_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1565_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1554_);
v___x_1567_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Nat_reprFast(v_i_1550_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 3);
lean_ctor_set(v___x_1558_, 0, v___x_1569_);
v___x_1571_ = v___x_1558_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1568_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_a_1556_);
v___x_1576_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_box(1);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_a_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1580_);
v___x_1582_ = v___x_1563_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_del_object(v___x_1558_);
lean_dec(v_a_1556_);
lean_dec(v_a_1554_);
lean_dec(v_i_1550_);
return v___x_1560_;
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v_k_1552_);
lean_dec(v_i_1550_);
return v___x_1555_;
}
}
else
{
lean_dec_ref(v_k_1552_);
lean_dec(v_y_1551_);
lean_dec(v_i_1550_);
return v___x_1553_;
}
}
case 9:
{
lean_object* v_fvarId_1587_; lean_object* v_i_1588_; lean_object* v_offset_1589_; lean_object* v_y_1590_; lean_object* v_ty_1591_; lean_object* v_k_1592_; lean_object* v_options_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_fvarId_1587_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1587_);
v_i_1588_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_i_1588_);
v_offset_1589_ = lean_ctor_get(v_c_1345_, 2);
lean_inc(v_offset_1589_);
v_y_1590_ = lean_ctor_get(v_c_1345_, 3);
lean_inc(v_y_1590_);
v_ty_1591_ = lean_ctor_get(v_c_1345_, 4);
lean_inc_ref(v_ty_1591_);
v_k_1592_ = lean_ctor_get(v_c_1345_, 5);
lean_inc_ref(v_k_1592_);
lean_dec_ref_known(v_c_1345_, 6);
v_options_1593_ = lean_ctor_get(v_a_1349_, 1);
v___x_1594_ = l_Lean_pp_letVarTypes;
v___x_1595_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v_ty_1591_);
v___x_1596_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1587_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1640_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1640_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1640_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1590_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1639_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1639_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1639_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1592_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1638_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1638_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1638_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1611_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_a_1597_);
v___x_1613_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Nat_reprFast(v_i_1588_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 3);
lean_ctor_set(v___x_1604_, 0, v___x_1615_);
v___x_1617_ = v___x_1604_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Nat_reprFast(v_offset_1589_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 3);
lean_ctor_set(v___x_1599_, 0, v___x_1621_);
v___x_1623_ = v___x_1599_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1620_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_a_1602_);
v___x_1628_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_box(1);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_a_1607_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1632_);
v___x_1634_ = v___x_1609_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
else
{
lean_del_object(v___x_1604_);
lean_dec(v_a_1602_);
lean_del_object(v___x_1599_);
lean_dec(v_a_1597_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1606_;
}
}
}
else
{
lean_del_object(v___x_1599_);
lean_dec(v_a_1597_);
lean_dec_ref(v_k_1592_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1601_;
}
}
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec(v_y_1590_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1596_;
}
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1587_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1591_, v_a_1346_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1690_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1690_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1690_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1590_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1689_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1689_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1689_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1592_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1688_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1688_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1688_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1658_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_a_1642_);
v___x_1660_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = l_Nat_reprFast(v_i_1588_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 3);
lean_ctor_set(v___x_1651_, 0, v___x_1662_);
v___x_1664_ = v___x_1651_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1661_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Nat_reprFast(v_offset_1589_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 3);
lean_ctor_set(v___x_1646_, 0, v___x_1668_);
v___x_1670_ = v___x_1646_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1667_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_a_1644_);
v___x_1675_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_a_1649_);
v___x_1678_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_box(1);
v___x_1681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v_a_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1682_);
v___x_1684_ = v___x_1656_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
else
{
lean_del_object(v___x_1651_);
lean_dec(v_a_1649_);
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
lean_dec(v_a_1642_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1653_;
}
}
}
else
{
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
lean_dec(v_a_1642_);
lean_dec_ref(v_k_1592_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1648_;
}
}
}
else
{
lean_dec(v_a_1642_);
lean_dec_ref(v_k_1592_);
lean_dec(v_y_1590_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1643_;
}
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_ty_1591_);
lean_dec(v_y_1590_);
lean_dec(v_offset_1589_);
lean_dec(v_i_1588_);
return v___x_1641_;
}
}
}
case 10:
{
lean_object* v_fvarId_1691_; lean_object* v_cidx_1692_; lean_object* v_k_1693_; lean_object* v___x_1694_; 
v_fvarId_1691_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1691_);
v_cidx_1692_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_cidx_1692_);
v_k_1693_ = lean_ctor_get(v_c_1345_, 2);
lean_inc_ref(v_k_1693_);
lean_dec_ref_known(v_c_1345_, 3);
v___x_1694_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1691_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1722_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1722_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1722_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1693_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1721_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1721_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1721_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1704_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1695_);
v___x_1706_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Nat_reprFast(v_cidx_1692_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 3);
lean_ctor_set(v___x_1697_, 0, v___x_1708_);
v___x_1710_ = v___x_1697_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1707_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_box(1);
v___x_1715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v_a_1700_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1716_);
v___x_1718_ = v___x_1702_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_del_object(v___x_1697_);
lean_dec(v_a_1695_);
lean_dec(v_cidx_1692_);
return v___x_1699_;
}
}
}
else
{
lean_dec_ref(v_k_1693_);
lean_dec(v_cidx_1692_);
return v___x_1694_;
}
}
case 11:
{
lean_object* v_fvarId_1723_; lean_object* v_n_1724_; uint8_t v_check_1725_; uint8_t v_persistent_1726_; lean_object* v_k_1727_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1796_; 
v_fvarId_1723_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1723_);
v_n_1724_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_n_1724_);
v_check_1725_ = lean_ctor_get_uint8(v_c_1345_, sizeof(void*)*3);
v_persistent_1726_ = lean_ctor_get_uint8(v_c_1345_, sizeof(void*)*3 + 1);
v_k_1727_ = lean_ctor_get(v_c_1345_, 2);
lean_inc_ref(v_k_1727_);
lean_dec_ref_known(v_c_1345_, 3);
if (v_persistent_1726_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1796_ = v___x_1799_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___y_1796_ = v___x_1800_;
goto v___jp_1795_;
}
v___jp_1728_:
{
lean_object* v_ann_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
lean_inc_ref(v___y_1729_);
v_ann_1731_ = lean_string_append(v___y_1729_, v___y_1730_);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_dec_eq(v_n_1724_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1723_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1766_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1766_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1766_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1727_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1765_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1765_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1765_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1745_ = l_Nat_reprFast(v_n_1724_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 3);
lean_ctor_set(v___x_1737_, 0, v___x_1745_);
v___x_1747_ = v___x_1737_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1744_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_ann_1731_);
v___x_1752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v_a_1735_);
v___x_1756_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_box(1);
v___x_1759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v_a_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1760_);
v___x_1762_ = v___x_1742_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_del_object(v___x_1737_);
lean_dec(v_a_1735_);
lean_dec_ref(v_ann_1731_);
lean_dec(v_n_1724_);
return v___x_1739_;
}
}
}
else
{
lean_dec_ref(v_ann_1731_);
lean_dec_ref(v_k_1727_);
lean_dec(v_n_1724_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_n_1724_);
v___x_1767_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1723_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1794_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1794_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1794_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1727_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1793_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1793_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1793_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 3);
lean_ctor_set(v___x_1770_, 0, v_ann_1731_);
v___x_1779_ = v___x_1770_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_ann_1731_);
v___x_1779_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1777_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1768_);
v___x_1784_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_box(1);
v___x_1787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v_a_1773_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1788_);
v___x_1790_ = v___x_1775_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_del_object(v___x_1770_);
lean_dec(v_a_1768_);
lean_dec_ref(v_ann_1731_);
return v___x_1772_;
}
}
}
else
{
lean_dec_ref(v_ann_1731_);
lean_dec_ref(v_k_1727_);
return v___x_1767_;
}
}
}
v___jp_1795_:
{
if (v_check_1725_ == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
v___y_1729_ = v___y_1796_;
v___y_1730_ = v___x_1797_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_1729_ = v___y_1796_;
v___y_1730_ = v___x_1798_;
goto v___jp_1728_;
}
}
}
case 12:
{
lean_object* v_fvarId_1801_; lean_object* v_n_1802_; uint8_t v_check_1803_; uint8_t v_persistent_1804_; lean_object* v_objs_x3f_1805_; lean_object* v_k_1806_; lean_object* v_ann_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v_ann_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v_ann_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; 
v_fvarId_1801_ = lean_ctor_get(v_c_1345_, 0);
lean_inc(v_fvarId_1801_);
v_n_1802_ = lean_ctor_get(v_c_1345_, 1);
lean_inc(v_n_1802_);
v_check_1803_ = lean_ctor_get_uint8(v_c_1345_, sizeof(void*)*4);
v_persistent_1804_ = lean_ctor_get_uint8(v_c_1345_, sizeof(void*)*4 + 1);
v_objs_x3f_1805_ = lean_ctor_get(v_c_1345_, 2);
lean_inc(v_objs_x3f_1805_);
v_k_1806_ = lean_ctor_get(v_c_1345_, 3);
lean_inc_ref(v_k_1806_);
lean_dec_ref_known(v_c_1345_, 4);
if (v_persistent_1804_ == 0)
{
lean_object* v_ann_1900_; 
v_ann_1900_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v_ann_1892_ = v_ann_1900_;
v___y_1893_ = v_a_1346_;
v___y_1894_ = v_a_1347_;
v___y_1895_ = v_a_1348_;
v___y_1896_ = v_a_1349_;
v___y_1897_ = v_a_1350_;
goto v___jp_1891_;
}
else
{
lean_object* v_ann_1901_; 
v_ann_1901_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v_ann_1892_ = v_ann_1901_;
v___y_1893_ = v_a_1346_;
v___y_1894_ = v_a_1347_;
v___y_1895_ = v_a_1348_;
v___y_1896_ = v_a_1349_;
v___y_1897_ = v_a_1350_;
goto v___jp_1891_;
}
v___jp_1807_:
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_nat_dec_eq(v_n_1802_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1801_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1848_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1848_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1848_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1806_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1847_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1847_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1847_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1826_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1827_ = l_Nat_reprFast(v_n_1802_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 3);
lean_ctor_set(v___x_1819_, 0, v___x_1827_);
v___x_1829_ = v___x_1819_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1826_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_ann_1808_);
v___x_1834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v_a_1817_);
v___x_1838_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_box(1);
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1842_);
v___x_1844_ = v___x_1824_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_del_object(v___x_1819_);
lean_dec(v_a_1817_);
lean_dec_ref(v_ann_1808_);
lean_dec(v_n_1802_);
return v___x_1821_;
}
}
}
else
{
lean_dec_ref(v_ann_1808_);
lean_dec_ref(v_k_1806_);
lean_dec(v_n_1802_);
return v___x_1816_;
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v_n_1802_);
v___x_1849_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1801_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1876_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1876_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1876_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1806_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1875_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1875_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1875_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 3);
lean_ctor_set(v___x_1852_, 0, v_ann_1808_);
v___x_1861_ = v___x_1852_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_ann_1808_);
v___x_1861_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_a_1850_);
v___x_1866_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_box(1);
v___x_1869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_a_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1870_);
v___x_1872_ = v___x_1857_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_del_object(v___x_1852_);
lean_dec(v_a_1850_);
lean_dec_ref(v_ann_1808_);
return v___x_1854_;
}
}
}
else
{
lean_dec_ref(v_ann_1808_);
lean_dec_ref(v_k_1806_);
return v___x_1849_;
}
}
}
v___jp_1877_:
{
if (lean_obj_tag(v_objs_x3f_1805_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v_ann_1890_; 
v_val_1884_ = lean_ctor_get(v_objs_x3f_1805_, 0);
lean_inc(v_val_1884_);
lean_dec_ref_known(v_objs_x3f_1805_, 1);
v___x_1885_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0));
v___x_1886_ = l_Nat_reprFast(v_val_1884_);
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__40));
v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
v_ann_1890_ = lean_string_append(v_ann_1878_, v___x_1889_);
lean_dec_ref(v___x_1889_);
v_ann_1808_ = v_ann_1890_;
v___y_1809_ = v___y_1879_;
v___y_1810_ = v___y_1880_;
v___y_1811_ = v___y_1881_;
v___y_1812_ = v___y_1882_;
v___y_1813_ = v___y_1883_;
goto v___jp_1807_;
}
else
{
lean_dec(v_objs_x3f_1805_);
v_ann_1808_ = v_ann_1878_;
v___y_1809_ = v___y_1879_;
v___y_1810_ = v___y_1880_;
v___y_1811_ = v___y_1881_;
v___y_1812_ = v___y_1882_;
v___y_1813_ = v___y_1883_;
goto v___jp_1807_;
}
}
v___jp_1891_:
{
if (v_check_1803_ == 0)
{
lean_object* v___x_1898_; lean_object* v_ann_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__34));
lean_inc_ref(v_ann_1892_);
v_ann_1899_ = lean_string_append(v_ann_1892_, v___x_1898_);
v_ann_1878_ = v_ann_1899_;
v___y_1879_ = v___y_1893_;
v___y_1880_ = v___y_1894_;
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___y_1896_;
v___y_1883_ = v___y_1897_;
goto v___jp_1877_;
}
else
{
lean_inc_ref(v_ann_1892_);
v_ann_1878_ = v_ann_1892_;
v___y_1879_ = v___y_1893_;
v___y_1880_ = v___y_1894_;
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___y_1896_;
v___y_1883_ = v___y_1897_;
goto v___jp_1877_;
}
}
}
default: 
{
lean_object* v_fvarId_1902_; lean_object* v_k_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1927_; 
v_fvarId_1902_ = lean_ctor_get(v_c_1345_, 0);
v_k_1903_ = lean_ctor_get(v_c_1345_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_c_1345_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1905_ = v_c_1345_;
v_isShared_1906_ = v_isSharedCheck_1927_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_k_1903_);
lean_inc(v_fvarId_1902_);
lean_dec(v_c_1345_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1927_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1902_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1344_, v_k_1903_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1926_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1926_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1926_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__42));
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 5);
lean_ctor_set(v___x_1905_, 1, v_a_1908_);
lean_ctor_set(v___x_1905_, 0, v___x_1914_);
v___x_1916_ = v___x_1905_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1908_);
v___x_1916_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1917_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_box(1);
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v_a_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1921_);
v___x_1923_ = v___x_1912_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_dec(v_a_1908_);
lean_del_object(v___x_1905_);
return v___x_1909_;
}
}
else
{
lean_del_object(v___x_1905_);
lean_dec_ref(v_k_1903_);
return v___x_1907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1928_, lean_object* v_funDecl_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_binderName_1936_; lean_object* v_params_1937_; lean_object* v_type_1938_; lean_object* v_value_1939_; lean_object* v___x_1940_; 
v_binderName_1936_ = lean_ctor_get(v_funDecl_1929_, 1);
lean_inc(v_binderName_1936_);
v_params_1937_ = lean_ctor_get(v_funDecl_1929_, 2);
lean_inc_ref(v_params_1937_);
v_type_1938_ = lean_ctor_get(v_funDecl_1929_, 3);
lean_inc_ref(v_type_1938_);
v_value_1939_ = lean_ctor_get(v_funDecl_1929_, 4);
lean_inc_ref(v_value_1939_);
lean_dec_ref(v_funDecl_1929_);
v___x_1940_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1928_, v_params_1937_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1928_, v_params_1937_, v_type_1938_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1943_, v_a_1930_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1971_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1971_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1971_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1928_, v_value_1939_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1970_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1970_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1970_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
uint8_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = 1;
v___x_1955_ = l_Lean_Name_toString(v_binderName_1936_, v___x_1954_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 3);
lean_ctor_set(v___x_1947_, 0, v___x_1955_);
v___x_1957_ = v___x_1947_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v_a_1941_);
v___x_1959_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_a_1945_);
v___x_1962_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Std_Format_indentD(v_a_1950_);
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1965_);
v___x_1967_ = v___x_1952_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_del_object(v___x_1947_);
lean_dec(v_a_1945_);
lean_dec(v_a_1941_);
lean_dec(v_binderName_1936_);
return v___x_1949_;
}
}
}
else
{
lean_dec(v_a_1941_);
lean_dec_ref(v_value_1939_);
lean_dec(v_binderName_1936_);
return v___x_1944_;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_a_1941_);
lean_dec_ref(v_value_1939_);
lean_dec(v_binderName_1936_);
v_a_1972_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1942_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1942_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_dec_ref(v_value_1939_);
lean_dec_ref(v_type_1938_);
lean_dec_ref(v_params_1937_);
lean_dec(v_binderName_1936_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_1980_, lean_object* v_funDecl_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v_pu_boxed_1988_; lean_object* v_res_1989_; 
v_pu_boxed_1988_ = lean_unbox(v_pu_1980_);
v_res_1989_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_1988_, v_funDecl_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_1990_, lean_object* v_c_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
uint8_t v_pu_boxed_1998_; lean_object* v_res_1999_; 
v_pu_boxed_1998_ = lean_unbox(v_pu_1990_);
v_res_1999_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_1998_, v_c_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_2003_, lean_object* v_b_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
if (lean_obj_tag(v_b_2004_) == 0)
{
lean_object* v_code_2011_; lean_object* v___x_2012_; 
v_code_2011_ = lean_ctor_get(v_b_2004_, 0);
lean_inc_ref(v_code_2011_);
lean_dec_ref_known(v_b_2004_, 1);
v___x_2012_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_2003_, v_code_2011_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
return v___x_2012_;
}
else
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v_b_2004_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_b_2004_, 0);
lean_dec(v_unused_2021_);
v___x_2014_ = v_b_2004_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_b_2004_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_2022_, lean_object* v_b_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
uint8_t v_pu_boxed_2030_; lean_object* v_res_2031_; 
v_pu_boxed_2030_ = lean_unbox(v_pu_2022_);
v_res_2031_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_2030_, v_b_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec_ref(v_a_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_2032_, lean_object* v_opt_2033_){
_start:
{
lean_object* v_name_2034_; lean_object* v_defValue_2035_; lean_object* v_map_2036_; lean_object* v___x_2037_; 
v_name_2034_ = lean_ctor_get(v_opt_2033_, 0);
v_defValue_2035_ = lean_ctor_get(v_opt_2033_, 1);
v_map_2036_ = lean_ctor_get(v_opts_2032_, 0);
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2036_, v_name_2034_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_inc(v_defValue_2035_);
return v_defValue_2035_;
}
else
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2037_, 1);
if (lean_obj_tag(v_val_2038_) == 3)
{
lean_object* v_v_2039_; 
v_v_2039_ = lean_ctor_get(v_val_2038_, 0);
lean_inc(v_v_2039_);
lean_dec_ref_known(v_val_2038_, 1);
return v_v_2039_;
}
else
{
lean_dec(v_val_2038_);
lean_inc(v_defValue_2035_);
return v_defValue_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_2040_, lean_object* v_opt_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_2040_, v_opt_2041_);
lean_dec_ref(v_opt_2041_);
lean_dec_ref(v_opts_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(lean_object* v_o_2046_, lean_object* v_k_2047_, uint8_t v_v_2048_){
_start:
{
lean_object* v_map_2049_; uint8_t v_hasTrace_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2064_; 
v_map_2049_ = lean_ctor_get(v_o_2046_, 0);
v_hasTrace_2050_ = lean_ctor_get_uint8(v_o_2046_, sizeof(void*)*1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_o_2046_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2052_ = v_o_2046_;
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_map_2049_);
lean_dec(v_o_2046_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2054_, 0, v_v_2048_);
lean_inc(v_k_2047_);
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2047_, v___x_2054_, v_map_2049_);
if (v_hasTrace_2050_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1));
v___x_2057_ = l_Lean_Name_isPrefixOf(v___x_2056_, v_k_2047_);
lean_dec(v_k_2047_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2059_ = v___x_2052_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2055_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*1, v___x_2057_);
return v___x_2059_;
}
}
else
{
lean_object* v___x_2062_; 
lean_dec(v_k_2047_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2062_ = v___x_2052_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*1, v_hasTrace_2050_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(lean_object* v_o_2065_, lean_object* v_k_2066_, lean_object* v_v_2067_){
_start:
{
uint8_t v_v_boxed_2068_; lean_object* v_res_2069_; 
v_v_boxed_2068_ = lean_unbox(v_v_2067_);
v_res_2069_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_o_2065_, v_k_2066_, v_v_boxed_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_2070_, lean_object* v_opt_2071_, uint8_t v_val_2072_){
_start:
{
lean_object* v_name_2073_; lean_object* v___x_2074_; 
v_name_2073_ = lean_ctor_get(v_opt_2071_, 0);
lean_inc(v_name_2073_);
lean_dec_ref(v_opt_2071_);
v___x_2074_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_opts_2070_, v_name_2073_, v_val_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_2075_, lean_object* v_opt_2076_, lean_object* v_val_2077_){
_start:
{
uint8_t v_val_boxed_2078_; lean_object* v_res_2079_; 
v_val_boxed_2078_ = lean_unbox(v_val_2077_);
v_res_2079_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_2075_, v_opt_2076_, v_val_boxed_2078_);
return v_res_2079_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v_options_2092_; lean_object* v_env_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2130_; uint8_t v___x_2151_; 
v___x_2091_ = lean_st_ref_get(v_a_2089_);
v_options_2092_ = lean_ctor_get(v_a_2088_, 1);
v_env_2093_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_ref(v_env_2093_);
lean_dec(v___x_2091_);
v___x_2094_ = l_Lean_pp_sanitizeNames;
v___x_2095_ = 0;
lean_inc_ref(v_options_2092_);
v___x_2096_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_options_2092_, v___x_2094_, v___x_2095_);
v___x_2097_ = l_Lean_diagnostics;
v___x_2098_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_2096_, v___x_2097_);
v___x_2151_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2093_);
lean_dec_ref(v_env_2093_);
if (v___x_2098_ == 0)
{
if (v___x_2151_ == 0)
{
v___y_2100_ = v_a_2088_;
v___y_2101_ = v_a_2089_;
goto v___jp_2099_;
}
else
{
v___y_2130_ = v___x_2098_;
goto v___jp_2129_;
}
}
else
{
v___y_2130_ = v___x_2151_;
goto v___jp_2129_;
}
v___jp_2099_:
{
lean_object* v___x_2102_; lean_object* v_toCold_2103_; lean_object* v_currRecDepth_2104_; lean_object* v_ref_2105_; lean_object* v_currNamespace_2106_; lean_object* v_openDecls_2107_; lean_object* v_initHeartbeats_2108_; lean_object* v_maxHeartbeats_2109_; lean_object* v_currMacroScope_2110_; uint8_t v_suppressElabErrors_2111_; lean_object* v___x_2112_; 
v___x_2102_ = lean_st_ref_get(v_a_2087_);
v_toCold_2103_ = lean_ctor_get(v___y_2100_, 0);
v_currRecDepth_2104_ = lean_ctor_get(v___y_2100_, 2);
v_ref_2105_ = lean_ctor_get(v___y_2100_, 4);
v_currNamespace_2106_ = lean_ctor_get(v___y_2100_, 5);
v_openDecls_2107_ = lean_ctor_get(v___y_2100_, 6);
v_initHeartbeats_2108_ = lean_ctor_get(v___y_2100_, 7);
v_maxHeartbeats_2109_ = lean_ctor_get(v___y_2100_, 8);
v_currMacroScope_2110_ = lean_ctor_get(v___y_2100_, 9);
v_suppressElabErrors_2111_ = lean_ctor_get_uint8(v___y_2100_, sizeof(void*)*10 + 1);
v___x_2112_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2086_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_lctx_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v_lctx_2114_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_lctx_2114_);
lean_dec(v___x_2102_);
v___x_2115_ = l_Lean_maxRecDepth;
v___x_2116_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v___x_2096_, v___x_2115_);
lean_inc(v_currMacroScope_2110_);
lean_inc(v_maxHeartbeats_2109_);
lean_inc(v_initHeartbeats_2108_);
lean_inc(v_openDecls_2107_);
lean_inc(v_currNamespace_2106_);
lean_inc(v_ref_2105_);
lean_inc(v_currRecDepth_2104_);
lean_inc_ref(v_toCold_2103_);
v___x_2117_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2117_, 0, v_toCold_2103_);
lean_ctor_set(v___x_2117_, 1, v___x_2096_);
lean_ctor_set(v___x_2117_, 2, v_currRecDepth_2104_);
lean_ctor_set(v___x_2117_, 3, v___x_2116_);
lean_ctor_set(v___x_2117_, 4, v_ref_2105_);
lean_ctor_set(v___x_2117_, 5, v_currNamespace_2106_);
lean_ctor_set(v___x_2117_, 6, v_openDecls_2107_);
lean_ctor_set(v___x_2117_, 7, v_initHeartbeats_2108_);
lean_ctor_set(v___x_2117_, 8, v_maxHeartbeats_2109_);
lean_ctor_set(v___x_2117_, 9, v_currMacroScope_2110_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*10, v___x_2098_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*10 + 1, v_suppressElabErrors_2111_);
v___x_2118_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
v___x_2119_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2114_, v___x_2118_);
lean_dec_ref(v_lctx_2114_);
lean_inc(v___y_2101_);
lean_inc(v_a_2087_);
lean_inc_ref(v_a_2086_);
v___x_2120_ = lean_apply_6(v_x_2085_, v___x_2119_, v_a_2086_, v_a_2087_, v___x_2117_, v___y_2101_, lean_box(0));
return v___x_2120_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v___x_2102_);
lean_dec_ref(v___x_2096_);
lean_dec_ref(v_x_2085_);
v_a_2121_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2112_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2112_);
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
v___jp_2129_:
{
if (v___y_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v_env_2132_; lean_object* v_nextMacroScope_2133_; lean_object* v_ngen_2134_; lean_object* v_auxDeclNGen_2135_; lean_object* v_traceState_2136_; lean_object* v_messages_2137_; lean_object* v_infoState_2138_; lean_object* v_snapshotTasks_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2149_; 
v___x_2131_ = lean_st_ref_take(v_a_2089_);
v_env_2132_ = lean_ctor_get(v___x_2131_, 0);
v_nextMacroScope_2133_ = lean_ctor_get(v___x_2131_, 1);
v_ngen_2134_ = lean_ctor_get(v___x_2131_, 2);
v_auxDeclNGen_2135_ = lean_ctor_get(v___x_2131_, 3);
v_traceState_2136_ = lean_ctor_get(v___x_2131_, 4);
v_messages_2137_ = lean_ctor_get(v___x_2131_, 6);
v_infoState_2138_ = lean_ctor_get(v___x_2131_, 7);
v_snapshotTasks_2139_ = lean_ctor_get(v___x_2131_, 8);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v___x_2131_, 5);
lean_dec(v_unused_2150_);
v___x_2141_ = v___x_2131_;
v_isShared_2142_ = v_isSharedCheck_2149_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snapshotTasks_2139_);
lean_inc(v_infoState_2138_);
lean_inc(v_messages_2137_);
lean_inc(v_traceState_2136_);
lean_inc(v_auxDeclNGen_2135_);
lean_inc(v_ngen_2134_);
lean_inc(v_nextMacroScope_2133_);
lean_inc(v_env_2132_);
lean_dec(v___x_2131_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2149_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2143_ = l_Lean_Kernel_enableDiag(v_env_2132_, v___x_2098_);
v___x_2144_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 5, v___x_2144_);
lean_ctor_set(v___x_2141_, 0, v___x_2143_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_nextMacroScope_2133_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_ngen_2134_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_auxDeclNGen_2135_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_traceState_2136_);
lean_ctor_set(v_reuseFailAlloc_2148_, 5, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2148_, 6, v_messages_2137_);
lean_ctor_set(v_reuseFailAlloc_2148_, 7, v_infoState_2138_);
lean_ctor_set(v_reuseFailAlloc_2148_, 8, v_snapshotTasks_2139_);
v___x_2146_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_st_ref_put(v_a_2089_, v___x_2146_);
v___y_2100_ = v_a_2088_;
v___y_2101_ = v_a_2089_;
goto v___jp_2099_;
}
}
}
else
{
v___y_2100_ = v_a_2088_;
v___y_2101_ = v_a_2089_;
goto v___jp_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2159_, lean_object* v_x_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_x_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2167_, v_x_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2175_, lean_object* v_code_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_box(v_pu_2175_);
v___x_2183_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2183_, 0, v___x_2182_);
lean_closure_set(v___x_2183_, 1, v_code_2176_);
v___x_2184_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2183_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2185_, lean_object* v_code_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
uint8_t v_pu_boxed_2192_; lean_object* v_res_2193_; 
v_pu_boxed_2192_ = lean_unbox(v_pu_2185_);
v_res_2193_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2192_, v_code_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2194_, lean_object* v_e_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_box(v_pu_2194_);
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2202_, 0, v___x_2201_);
lean_closure_set(v___x_2202_, 1, v_e_2195_);
v___x_2203_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2202_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2204_, lean_object* v_e_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
uint8_t v_pu_boxed_2211_; lean_object* v_res_2212_; 
v_pu_boxed_2211_ = lean_unbox(v_pu_2204_);
v_res_2212_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2211_, v_e_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2216_, lean_object* v_params_2217_, lean_object* v_type_2218_, lean_object* v_value_2219_, lean_object* v_name_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2216_, v_params_2217_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2216_, v_params_2217_, v_type_2218_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2230_, v___y_2221_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2260_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2260_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2260_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2216_, v_value_2219_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2259_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2259_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2259_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2241_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2242_ = 1;
v___x_2243_ = l_Lean_Name_toString(v_name_2220_, v___x_2242_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 3);
lean_ctor_set(v___x_2234_, 0, v___x_2243_);
v___x_2245_ = v___x_2234_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2241_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v_a_2228_);
v___x_2248_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_a_2232_);
v___x_2251_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Std_Format_indentD(v_a_2237_);
v___x_2254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2254_);
v___x_2256_ = v___x_2239_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_del_object(v___x_2234_);
lean_dec(v_a_2232_);
lean_dec(v_a_2228_);
lean_dec(v_name_2220_);
return v___x_2236_;
}
}
}
else
{
lean_dec(v_a_2228_);
lean_dec(v_name_2220_);
lean_dec_ref(v_value_2219_);
return v___x_2231_;
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_a_2228_);
lean_dec(v_name_2220_);
lean_dec_ref(v_value_2219_);
v_a_2261_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2229_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2229_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_dec(v_name_2220_);
lean_dec_ref(v_value_2219_);
lean_dec_ref(v_type_2218_);
lean_dec_ref(v_params_2217_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2269_, lean_object* v_params_2270_, lean_object* v_type_2271_, lean_object* v_value_2272_, lean_object* v_name_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v_pu_boxed_2280_; lean_object* v_res_2281_; 
v_pu_boxed_2280_ = lean_unbox(v_pu_2269_);
v_res_2281_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2280_, v_params_2270_, v_type_2271_, v_value_2272_, v_name_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2282_, lean_object* v_decl_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_toSignature_2289_; lean_object* v_value_2290_; lean_object* v_name_2291_; lean_object* v_type_2292_; lean_object* v_params_2293_; lean_object* v___x_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; 
v_toSignature_2289_ = lean_ctor_get(v_decl_2283_, 0);
lean_inc_ref(v_toSignature_2289_);
v_value_2290_ = lean_ctor_get(v_decl_2283_, 1);
lean_inc_ref(v_value_2290_);
lean_dec_ref(v_decl_2283_);
v_name_2291_ = lean_ctor_get(v_toSignature_2289_, 0);
lean_inc(v_name_2291_);
v_type_2292_ = lean_ctor_get(v_toSignature_2289_, 2);
lean_inc_ref(v_type_2292_);
v_params_2293_ = lean_ctor_get(v_toSignature_2289_, 3);
lean_inc_ref(v_params_2293_);
lean_dec_ref(v_toSignature_2289_);
v___x_2294_ = lean_box(v_pu_2282_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2295_, 0, v___x_2294_);
lean_closure_set(v___f_2295_, 1, v_params_2293_);
lean_closure_set(v___f_2295_, 2, v_type_2292_);
lean_closure_set(v___f_2295_, 3, v_value_2290_);
lean_closure_set(v___f_2295_, 4, v_name_2291_);
v___x_2296_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2295_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2297_, lean_object* v_decl_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
uint8_t v_pu_boxed_2304_; lean_object* v_res_2305_; 
v_pu_boxed_2304_ = lean_unbox(v_pu_2297_);
v_res_2305_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2304_, v_decl_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2306_, lean_object* v_decl_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2306_, v_decl_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2324_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2324_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2324_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2319_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v_a_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2320_);
v___x_2322_ = v___x_2317_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2325_, lean_object* v_decl_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v_pu_boxed_2333_; lean_object* v_res_2334_; 
v_pu_boxed_2333_ = lean_unbox(v_pu_2325_);
v_res_2334_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2333_, v_decl_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2335_, lean_object* v_decl_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(v_pu_2335_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2343_, 0, v___x_2342_);
lean_closure_set(v___f_2343_, 1, v_decl_2336_);
v___x_2344_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2343_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2345_, lean_object* v_decl_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
uint8_t v_pu_boxed_2352_; lean_object* v_res_2353_; 
v_pu_boxed_2352_ = lean_unbox(v_pu_2345_);
v_res_2353_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2352_, v_decl_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2354_, lean_object* v_val_2355_, lean_object* v_a_x3f_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_st_ref_swap(v_a_2354_, v_val_2355_);
lean_dec(v___x_2358_);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2361_, lean_object* v_val_2362_, lean_object* v_a_x3f_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2361_, v_val_2362_, v_a_x3f_2363_);
lean_dec(v_a_x3f_2363_);
lean_dec(v_a_2361_);
return v_res_2365_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_unsigned_to_nat(16u);
v___x_2368_ = lean_mk_array(v___x_2367_, v___x_2366_);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2370_ = lean_unsigned_to_nat(0u);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2373_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
lean_ctor_set(v___x_2373_, 3, v___x_2372_);
lean_ctor_set(v___x_2373_, 4, v___x_2372_);
lean_ctor_set(v___x_2373_, 5, v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2377_, lean_object* v_x_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_r_2384_; 
v___x_2382_ = lean_st_ref_get(v_a_2380_);
v___x_2383_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2384_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2378_, v___x_2383_, v_phase_2377_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v_r_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2401_; 
v_a_2385_ = lean_ctor_get(v_r_2384_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_r_2384_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2387_ = v_r_2384_;
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v_r_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
lean_inc(v_a_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 1);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v___x_2391_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2380_, v___x_2382_, v___x_2390_);
lean_dec_ref(v___x_2390_);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2399_);
v___x_2393_ = v___x_2391_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v___x_2391_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_a_2385_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2385_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2402_ = lean_ctor_get(v_r_2384_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v_r_2384_, 1);
v___x_2403_ = lean_box(0);
v___x_2404_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2380_, v___x_2382_, v___x_2403_);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2412_);
v___x_2406_ = v___x_2404_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v___x_2404_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 1);
lean_ctor_set(v___x_2406_, 0, v_a_2402_);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2402_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2413_, lean_object* v_x_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
uint8_t v_phase_boxed_2418_; lean_object* v_res_2419_; 
v_phase_boxed_2418_ = lean_unbox(v_phase_2413_);
v_res_2419_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2418_, v_x_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2420_, uint8_t v_phase_2421_, lean_object* v_x_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2421_, v_x_2422_, v_a_2423_, v_a_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_phase_2428_, lean_object* v_x_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
uint8_t v_phase_boxed_2433_; lean_object* v_res_2434_; 
v_phase_boxed_2433_ = lean_unbox(v_phase_2428_);
v_res_2434_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2427_, v_phase_boxed_2433_, v_x_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2435_, lean_object* v_decl_2436_, lean_object* v___x_2437_, uint8_t v___x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2435_, v_decl_2436_, v___x_2437_, v___x_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2435_, v_a_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2446_;
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2444_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2444_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2455_, lean_object* v_decl_2456_, lean_object* v___x_2457_, lean_object* v___x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
uint8_t v_pu_boxed_2464_; uint8_t v___x_99__boxed_2465_; lean_object* v_res_2466_; 
v_pu_boxed_2464_ = lean_unbox(v_pu_2455_);
v___x_99__boxed_2465_ = lean_unbox(v___x_2458_);
v_res_2466_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2464_, v_decl_2456_, v___x_2457_, v___x_99__boxed_2465_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2467_, lean_object* v_decl_2468_, uint8_t v_phase_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
v___x_2473_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2474_ = 0;
v___x_2475_ = lean_box(v_pu_2467_);
v___x_2476_ = lean_box(v___x_2474_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2477_, 0, v___x_2475_);
lean_closure_set(v___f_2477_, 1, v_decl_2468_);
lean_closure_set(v___f_2477_, 2, v___x_2473_);
lean_closure_set(v___f_2477_, 3, v___x_2476_);
v___x_2478_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2469_, v___f_2477_, v_a_2470_, v_a_2471_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2479_, lean_object* v_decl_2480_, lean_object* v_phase_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
uint8_t v_pu_boxed_2485_; uint8_t v_phase_boxed_2486_; lean_object* v_res_2487_; 
v_pu_boxed_2485_ = lean_unbox(v_pu_2479_);
v_phase_boxed_2486_ = lean_unbox(v_phase_2481_);
v_res_2487_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2485_, v_decl_2480_, v_phase_boxed_2486_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2488_, lean_object* v_code_2489_, lean_object* v___x_2490_, uint8_t v___x_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2488_, v_code_2489_, v___x_2490_, v___x_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2488_, v_a_2498_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2499_;
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2497_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2497_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2508_, lean_object* v_code_2509_, lean_object* v___x_2510_, lean_object* v___x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
uint8_t v_pu_boxed_2517_; uint8_t v___x_99__boxed_2518_; lean_object* v_res_2519_; 
v_pu_boxed_2517_ = lean_unbox(v_pu_2508_);
v___x_99__boxed_2518_ = lean_unbox(v___x_2511_);
v_res_2519_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2517_, v_code_2509_, v___x_2510_, v___x_99__boxed_2518_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2520_, lean_object* v_code_2521_, uint8_t v_phase_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; 
v___x_2526_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2527_ = 0;
v___x_2528_ = lean_box(v_pu_2520_);
v___x_2529_ = lean_box(v___x_2527_);
v___f_2530_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2530_, 0, v___x_2528_);
lean_closure_set(v___f_2530_, 1, v_code_2521_);
lean_closure_set(v___f_2530_, 2, v___x_2526_);
lean_closure_set(v___f_2530_, 3, v___x_2529_);
v___x_2531_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2522_, v___f_2530_, v_a_2523_, v_a_2524_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2532_, lean_object* v_code_2533_, lean_object* v_phase_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
uint8_t v_pu_boxed_2538_; uint8_t v_phase_boxed_2539_; lean_object* v_res_2540_; 
v_pu_boxed_2538_ = lean_unbox(v_pu_2532_);
v_phase_boxed_2539_ = lean_unbox(v_phase_2534_);
v_res_2540_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2538_, v_code_2533_, v_phase_boxed_2539_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2540_;
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

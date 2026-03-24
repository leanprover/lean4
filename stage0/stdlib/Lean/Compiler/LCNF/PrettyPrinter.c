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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inc "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__32 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dec["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__34 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__35 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dec "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__37 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "del "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__38 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__39 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value;
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
lean_dec_ref(v___x_24_);
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
lean_dec_ref(v___x_60_);
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
lean_dec_ref(v___x_137_);
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
v___x_311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_309_);
lean_ctor_set(v___x_311_, 4, v___x_309_);
lean_ctor_set(v___x_311_, 5, v___x_309_);
lean_ctor_set(v___x_311_, 6, v___x_309_);
lean_ctor_set(v___x_311_, 7, v___x_309_);
lean_ctor_set(v___x_311_, 8, v___x_309_);
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
lean_dec_ref(v___x_343_);
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
lean_dec_ref(v___x_383_);
if (lean_obj_tag(v_val_385_) == 1)
{
uint8_t v_v_386_; 
v_v_386_ = lean_ctor_get_uint8(v_val_385_, 0);
lean_dec_ref(v_val_385_);
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
lean_dec_ref(v_e_410_);
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
v_options_425_ = lean_ctor_get(v_a_414_, 2);
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
lean_dec_ref(v_lit_507_);
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
lean_dec_ref(v_lit_507_);
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
lean_dec_ref(v_lit_507_);
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
lean_object* v_name_583_; lean_object* v_cidx_584_; lean_object* v_usize_585_; lean_object* v_ssize_586_; lean_object* v_r_588_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_r_602_; uint8_t v___y_604_; lean_object* v___x_614_; uint8_t v___x_615_; 
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
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_lt(v___x_614_, v_usize_585_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v___x_614_, v_ssize_586_);
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_615_;
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
if (v___y_604_ == 0)
{
lean_dec(v_ssize_586_);
lean_dec(v_usize_585_);
v_r_588_ = v_r_602_;
goto v___jp_587_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_r_613_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v_r_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Nat_reprFast(v_usize_585_);
v___x_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_605_);
v___x_611_ = l_Nat_reprFast(v_ssize_586_);
v___x_612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v_r_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_613_, 0, v___x_610_);
lean_ctor_set(v_r_613_, 1, v___x_612_);
v_r_588_ = v_r_613_;
goto v___jp_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* v_a_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_a_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t v_pu_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
switch(lean_obj_tag(v_e_667_))
{
case 0:
{
lean_object* v_value_674_; lean_object* v___x_675_; 
v_value_674_ = lean_ctor_get(v_e_667_, 0);
lean_inc_ref(v_value_674_);
lean_dec_ref(v_e_667_);
v___x_675_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_674_);
return v___x_675_;
}
case 1:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
case 2:
{
lean_object* v_idx_678_; lean_object* v_struct_679_; lean_object* v___x_680_; 
v_idx_678_ = lean_ctor_get(v_e_667_, 1);
lean_inc(v_idx_678_);
v_struct_679_ = lean_ctor_get(v_e_667_, 2);
lean_inc(v_struct_679_);
lean_dec_ref(v_e_667_);
v___x_680_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_struct_679_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_693_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_693_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_685_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v_a_681_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Nat_reprFast(v_idx_678_);
v___x_688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_686_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_689_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_dec(v_idx_678_);
return v___x_680_;
}
}
case 3:
{
lean_object* v_declName_694_; lean_object* v_us_695_; lean_object* v_args_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_declName_694_ = lean_ctor_get(v_e_667_, 0);
lean_inc(v_declName_694_);
v_us_695_ = lean_ctor_get(v_e_667_, 1);
lean_inc(v_us_695_);
v_args_696_ = lean_ctor_get(v_e_667_, 2);
lean_inc_ref(v_args_696_);
lean_dec_ref(v_e_667_);
v___x_697_ = l_Lean_Expr_const___override(v_declName_694_, v_us_695_);
v___x_698_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v___x_697_, v_a_668_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_696_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_696_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_709_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_709_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v_a_699_);
lean_ctor_set(v___x_705_, 1, v_a_701_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_dec(v_a_699_);
return v___x_700_;
}
}
else
{
lean_dec_ref(v_args_696_);
return v___x_698_;
}
}
case 4:
{
lean_object* v_fvarId_710_; lean_object* v_args_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_729_; 
v_fvarId_710_ = lean_ctor_get(v_e_667_, 0);
v_args_711_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_729_ == 0)
{
v___x_713_ = v_e_667_;
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_args_711_);
lean_inc(v_fvarId_710_);
lean_dec(v_e_667_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_710_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref(v___x_715_);
v___x_717_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_711_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_711_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_728_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_728_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 5);
lean_ctor_set(v___x_713_, 1, v_a_718_);
lean_ctor_set(v___x_713_, 0, v_a_716_);
v___x_723_ = v___x_713_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_716_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_a_718_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_725_ = v___x_720_;
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
}
else
{
lean_dec(v_a_716_);
lean_del_object(v___x_713_);
return v___x_717_;
}
}
else
{
lean_del_object(v___x_713_);
lean_dec_ref(v_args_711_);
return v___x_715_;
}
}
}
case 5:
{
lean_object* v_i_730_; lean_object* v_args_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_748_; 
v_i_730_ = lean_ctor_get(v_e_667_, 0);
v_args_731_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_748_ == 0)
{
v___x_733_ = v_e_667_;
v_isShared_734_ = v_isSharedCheck_748_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_args_731_);
lean_inc(v_i_730_);
lean_dec(v_e_667_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_748_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_731_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_747_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_747_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_730_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_736_);
lean_ctor_set(v___x_733_, 0, v___x_740_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_a_736_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_del_object(v___x_733_);
lean_dec_ref(v_i_730_);
return v___x_735_;
}
}
}
case 6:
{
lean_object* v_i_749_; lean_object* v_var_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_772_; 
v_i_749_ = lean_ctor_get(v_e_667_, 0);
v_var_750_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_772_ == 0)
{
v___x_752_ = v_e_667_;
v_isShared_753_ = v_isSharedCheck_772_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_var_750_);
lean_inc(v_i_749_);
lean_dec(v_e_667_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_772_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_750_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_771_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_759_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
v___x_760_ = l_Nat_reprFast(v_i_749_);
v___x_761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 5);
lean_ctor_set(v___x_752_, 1, v___x_761_);
lean_ctor_set(v___x_752_, 0, v___x_759_);
v___x_763_ = v___x_752_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_770_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_764_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_768_ = v___x_757_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_del_object(v___x_752_);
lean_dec(v_i_749_);
return v___x_754_;
}
}
}
case 7:
{
lean_object* v_i_773_; lean_object* v_var_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_796_; 
v_i_773_ = lean_ctor_get(v_e_667_, 0);
v_var_774_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_796_ == 0)
{
v___x_776_ = v_e_667_;
v_isShared_777_ = v_isSharedCheck_796_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_var_774_);
lean_inc(v_i_773_);
lean_dec(v_e_667_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_796_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_774_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_795_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_795_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_795_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_783_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
v___x_784_ = l_Nat_reprFast(v_i_773_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 5);
lean_ctor_set(v___x_776_, 1, v___x_785_);
lean_ctor_set(v___x_776_, 0, v___x_783_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_794_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_788_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_790_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_del_object(v___x_776_);
lean_dec(v_i_773_);
return v___x_778_;
}
}
}
case 8:
{
lean_object* v_n_797_; lean_object* v_offset_798_; lean_object* v_var_799_; lean_object* v___x_800_; 
v_n_797_ = lean_ctor_get(v_e_667_, 0);
lean_inc(v_n_797_);
v_offset_798_ = lean_ctor_get(v_e_667_, 1);
lean_inc(v_offset_798_);
v_var_799_ = lean_ctor_get(v_e_667_, 2);
lean_inc(v_var_799_);
lean_dec_ref(v_e_667_);
v___x_800_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_799_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_820_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_820_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_805_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
v___x_806_ = l_Nat_reprFast(v_n_797_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Nat_reprFast(v_offset_798_);
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_810_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_a_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_816_);
v___x_818_ = v___x_803_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_dec(v_offset_798_);
lean_dec(v_n_797_);
return v___x_800_;
}
}
case 9:
{
lean_object* v_fn_821_; lean_object* v_args_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_841_; 
v_fn_821_ = lean_ctor_get(v_e_667_, 0);
v_args_822_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_841_ == 0)
{
v___x_824_ = v_e_667_;
v_isShared_825_ = v_isSharedCheck_841_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_args_822_);
lean_inc(v_fn_821_);
lean_dec(v_e_667_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_841_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_822_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_822_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_840_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_840_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_831_ = 1;
v___x_832_ = l_Lean_Name_toString(v_fn_821_, v___x_831_);
v___x_833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 5);
lean_ctor_set(v___x_824_, 1, v_a_827_);
lean_ctor_set(v___x_824_, 0, v___x_833_);
v___x_835_ = v___x_824_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_a_827_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_835_);
v___x_837_ = v___x_829_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_del_object(v___x_824_);
lean_dec(v_fn_821_);
return v___x_826_;
}
}
}
case 10:
{
lean_object* v_fn_842_; lean_object* v_args_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_864_; 
v_fn_842_ = lean_ctor_get(v_e_667_, 0);
v_args_843_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_864_ == 0)
{
v___x_845_ = v_e_667_;
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_args_843_);
lean_inc(v_fn_842_);
lean_dec(v_e_667_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_843_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_843_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_863_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_863_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_852_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
v___x_853_ = 1;
v___x_854_ = l_Lean_Name_toString(v_fn_842_, v___x_853_);
v___x_855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 5);
lean_ctor_set(v___x_845_, 1, v___x_855_);
lean_ctor_set(v___x_845_, 0, v___x_852_);
v___x_857_ = v___x_845_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_862_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
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
lean_del_object(v___x_845_);
lean_dec(v_fn_842_);
return v___x_847_;
}
}
}
case 11:
{
lean_object* v_n_865_; lean_object* v_var_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_888_; 
v_n_865_ = lean_ctor_get(v_e_667_, 0);
v_var_866_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_888_ == 0)
{
v___x_868_ = v_e_667_;
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_var_866_);
lean_inc(v_n_865_);
lean_dec(v_e_667_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_866_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_887_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15));
v___x_876_ = l_Nat_reprFast(v_n_865_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 5);
lean_ctor_set(v___x_868_, 1, v___x_877_);
lean_ctor_set(v___x_868_, 0, v___x_875_);
v___x_879_ = v___x_868_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_886_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_880_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_882_);
v___x_884_ = v___x_873_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_del_object(v___x_868_);
lean_dec(v_n_865_);
return v___x_870_;
}
}
}
case 12:
{
lean_object* v_var_889_; lean_object* v_i_890_; uint8_t v_updateHeader_891_; lean_object* v_args_892_; lean_object* v___x_893_; 
v_var_889_ = lean_ctor_get(v_e_667_, 0);
lean_inc(v_var_889_);
v_i_890_ = lean_ctor_get(v_e_667_, 1);
lean_inc_ref(v_i_890_);
v_updateHeader_891_ = lean_ctor_get_uint8(v_e_667_, sizeof(void*)*3);
v_args_892_ = lean_ctor_get(v_e_667_, 2);
lean_inc_ref(v_args_892_);
lean_dec_ref(v_e_667_);
v___x_893_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_var_889_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_666_, v_args_892_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec_ref(v_args_892_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_917_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_917_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___y_902_; 
v___x_900_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17));
if (v_updateHeader_891_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21));
v___y_902_ = v___x_915_;
goto v___jp_901_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23));
v___y_902_ = v___x_916_;
goto v___jp_901_;
}
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___y_902_);
v___x_904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_a_894_);
v___x_906_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19));
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_890_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v_a_896_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_903_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_911_);
v___x_913_ = v___x_898_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_dec(v_a_894_);
lean_dec_ref(v_i_890_);
return v___x_895_;
}
}
else
{
lean_dec_ref(v_args_892_);
lean_dec_ref(v_i_890_);
return v___x_893_;
}
}
case 13:
{
lean_object* v_fvarId_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_935_; 
v_fvarId_918_ = lean_ctor_get(v_e_667_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_e_667_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_e_667_, 0);
lean_dec(v_unused_936_);
v___x_920_ = v_e_667_;
v_isShared_921_ = v_isSharedCheck_935_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_fvarId_918_);
lean_dec(v_e_667_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_935_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_918_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_934_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_934_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25));
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 5);
lean_ctor_set(v___x_920_, 1, v_a_923_);
lean_ctor_set(v___x_920_, 0, v___x_927_);
v___x_929_ = v___x_920_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_a_923_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_929_);
v___x_931_ = v___x_925_;
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
lean_del_object(v___x_920_);
return v___x_922_;
}
}
}
case 14:
{
lean_object* v_fvarId_937_; lean_object* v___x_938_; 
v_fvarId_937_ = lean_ctor_get(v_e_667_, 0);
lean_inc(v_fvarId_937_);
lean_dec_ref(v_e_667_);
v___x_938_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_937_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27));
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
return v___x_938_;
}
}
default: 
{
lean_object* v_fvarId_949_; lean_object* v___x_950_; 
v_fvarId_949_ = lean_ctor_get(v_e_667_, 0);
lean_inc(v_fvarId_949_);
lean_dec_ref(v_e_667_);
v___x_950_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_949_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_960_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_960_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_960_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_955_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v_a_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* v_pu_961_, lean_object* v_e_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
uint8_t v_pu_boxed_969_; lean_object* v_res_970_; 
v_pu_boxed_969_ = lean_unbox(v_pu_961_);
v_res_970_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_boxed_969_, v_e_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* v_param_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_binderName_980_; lean_object* v_type_981_; uint8_t v_borrow_982_; lean_object* v___y_984_; 
v_binderName_980_ = lean_ctor_get(v_param_975_, 1);
lean_inc(v_binderName_980_);
v_type_981_ = lean_ctor_get(v_param_975_, 2);
lean_inc_ref(v_type_981_);
v_borrow_982_ = lean_ctor_get_uint8(v_param_975_, sizeof(void*)*3);
lean_dec_ref(v_param_975_);
if (v_borrow_982_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20));
v___y_984_ = v___x_1017_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
v___y_984_ = v___x_1018_;
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v_options_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_options_985_ = lean_ctor_get(v_a_977_, 2);
v___x_986_ = l_Lean_pp_funBinderTypes;
v___x_987_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_985_, v___x_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_type_981_);
v___x_988_ = 1;
v___x_989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_binderName_980_, v___x_988_);
v___x_990_ = lean_string_append(v___y_984_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_981_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1016_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1016_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1016_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_998_ = l_Lean_Name_toString(v_binderName_980_, v___x_987_);
v___x_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___y_984_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_994_);
v___x_1005_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7, &l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
v___x_1006_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1004_);
v___x_1008_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1005_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = 0;
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_1011_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1012_);
v___x_1014_ = v___x_996_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_dec_ref(v___y_984_);
lean_dec(v_binderName_980_);
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* v_param_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t v_pu_1025_, lean_object* v_param_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_1026_, v_a_1027_, v_a_1030_, v_a_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* v_pu_1034_, lean_object* v_param_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
uint8_t v_pu_boxed_1042_; lean_object* v_res_1043_; 
v_pu_boxed_1042_ = lean_unbox(v_pu_1034_);
v_res_1043_ = l_Lean_Compiler_LCNF_PP_ppParam(v_pu_boxed_1042_, v_param_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t v_pu_1044_, lean_object* v_params_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
v___x_1053_ = lean_box(v_pu_1044_);
v___x_1054_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1052_, v_params_1045_, v___x_1054_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* v_pu_1056_, lean_object* v_params_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
uint8_t v_pu_boxed_1064_; lean_object* v_res_1065_; 
v_pu_boxed_1064_ = lean_unbox(v_pu_1056_);
v_res_1065_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_boxed_1064_, v_params_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_params_1057_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t v_pu_1072_, lean_object* v_letDecl_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_options_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_options_1080_ = lean_ctor_get(v_a_1077_, 2);
v___x_1081_ = l_Lean_pp_letVarTypes;
v___x_1082_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v_binderName_1083_; lean_object* v_value_1084_; lean_object* v___x_1085_; 
v_binderName_1083_ = lean_ctor_get(v_letDecl_1073_, 1);
lean_inc(v_binderName_1083_);
v_value_1084_ = lean_ctor_get(v_letDecl_1073_, 3);
lean_inc(v_value_1084_);
lean_dec_ref(v_letDecl_1073_);
v___x_1085_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1072_, v_value_1084_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1101_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1101_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1101_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1091_ = 1;
v___x_1092_ = l_Lean_Name_toString(v_binderName_1083_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1090_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1097_);
v___x_1099_ = v___x_1088_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_dec(v_binderName_1083_);
return v___x_1085_;
}
}
else
{
lean_object* v_binderName_1102_; lean_object* v_type_1103_; lean_object* v_value_1104_; lean_object* v___x_1105_; 
v_binderName_1102_ = lean_ctor_get(v_letDecl_1073_, 1);
lean_inc(v_binderName_1102_);
v_type_1103_ = lean_ctor_get(v_letDecl_1073_, 2);
lean_inc_ref(v_type_1103_);
v_value_1104_ = lean_ctor_get(v_letDecl_1073_, 3);
lean_inc(v_value_1104_);
lean_dec_ref(v_letDecl_1073_);
v___x_1105_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1103_, v_a_1074_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1131_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Compiler_LCNF_PP_ppLetValue(v_pu_1072_, v_value_1104_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1130_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
v___x_1116_ = l_Lean_Name_toString(v_binderName_1102_, v___x_1082_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 3);
lean_ctor_set(v___x_1108_, 0, v___x_1116_);
v___x_1118_ = v___x_1108_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1115_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_a_1106_);
v___x_1123_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_a_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1125_);
v___x_1127_ = v___x_1113_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_del_object(v___x_1108_);
lean_dec(v_a_1106_);
lean_dec(v_binderName_1102_);
return v___x_1110_;
}
}
}
else
{
lean_dec(v_value_1104_);
lean_dec(v_binderName_1102_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* v_pu_1132_, lean_object* v_letDecl_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
uint8_t v_pu_boxed_1140_; lean_object* v_res_1141_; 
v_pu_boxed_1140_ = lean_unbox(v_pu_1132_);
v_res_1141_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_boxed_1140_, v_letDecl_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_bs_1144_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1145_ == 0)
{
return v_bs_1144_;
}
else
{
lean_object* v_v_1146_; lean_object* v_fvarId_1147_; lean_object* v___x_1148_; lean_object* v_bs_x27_1149_; lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v_v_1146_ = lean_array_uget_borrowed(v_bs_1144_, v_i_1143_);
v_fvarId_1147_ = lean_ctor_get(v_v_1146_, 0);
lean_inc(v_fvarId_1147_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v_bs_x27_1149_ = lean_array_uset(v_bs_1144_, v_i_1143_, v___x_1148_);
v___x_1150_ = l_Lean_mkFVar(v_fvarId_1147_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1143_, v___x_1151_);
v___x_1153_ = lean_array_uset(v_bs_x27_1149_, v_i_1143_, v___x_1150_);
v_i_1143_ = v___x_1152_;
v_bs_1144_ = v___x_1153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_bs_1157_){
_start:
{
size_t v_sz_boxed_1158_; size_t v_i_boxed_1159_; lean_object* v_res_1160_; 
v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1159_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t v_pu_1161_, lean_object* v_ps_1162_, lean_object* v_type_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = l_Lean_Expr_isErased(v_type_1163_);
if (v___x_1167_ == 0)
{
if (v_pu_1161_ == 0)
{
size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_sz_1168_ = lean_array_size(v_ps_1162_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_1168_, v___x_1169_, v_ps_1162_);
v___x_1171_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_1163_, v___x_1170_, v_a_1164_, v_a_1165_);
lean_dec_ref(v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; 
lean_dec_ref(v_ps_1162_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_type_1163_);
return v___x_1172_;
}
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref(v_ps_1162_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_type_1163_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* v_pu_1174_, lean_object* v_ps_1175_, lean_object* v_type_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
uint8_t v_pu_boxed_1180_; lean_object* v_res_1181_; 
v_pu_boxed_1180_ = lean_unbox(v_pu_1174_);
v_res_1181_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_boxed_1180_, v_ps_1175_, v_type_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t v_pu_1206_, lean_object* v_alt_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
switch(lean_obj_tag(v_alt_1207_))
{
case 0:
{
lean_object* v_ctorName_1214_; lean_object* v_params_1215_; lean_object* v_code_1216_; lean_object* v___x_1217_; 
v_ctorName_1214_ = lean_ctor_get(v_alt_1207_, 0);
lean_inc(v_ctorName_1214_);
v_params_1215_ = lean_ctor_get(v_alt_1207_, 1);
lean_inc_ref(v_params_1215_);
v_code_1216_ = lean_ctor_get(v_alt_1207_, 2);
lean_inc_ref(v_code_1216_);
lean_dec_ref(v_alt_1207_);
v___x_1217_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1206_, v_params_1215_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec_ref(v_params_1215_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1243_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1243_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1243_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1206_, v_code_1216_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1242_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1227_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1228_ = 1;
v___x_1229_ = l_Lean_Name_toString(v_ctorName_1214_, v___x_1228_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 3);
lean_ctor_set(v___x_1220_, 0, v___x_1229_);
v___x_1231_ = v___x_1220_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1227_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v_a_1218_);
v___x_1234_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Std_Format_indentD(v_a_1223_);
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1237_);
v___x_1239_ = v___x_1225_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_del_object(v___x_1220_);
lean_dec(v_a_1218_);
lean_dec(v_ctorName_1214_);
return v___x_1222_;
}
}
}
else
{
lean_dec_ref(v_code_1216_);
lean_dec(v_ctorName_1214_);
return v___x_1217_;
}
}
case 1:
{
lean_object* v_info_1244_; lean_object* v_code_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1270_; 
v_info_1244_ = lean_ctor_get(v_alt_1207_, 0);
v_code_1245_ = lean_ctor_get(v_alt_1207_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_alt_1207_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1247_ = v_alt_1207_;
v_isShared_1248_ = v_isSharedCheck_1270_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_code_1245_);
lean_inc(v_info_1244_);
lean_dec(v_alt_1207_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1270_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1206_, v_code_1245_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1269_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1269_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1269_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_name_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v_name_1254_ = lean_ctor_get(v_info_1244_, 0);
lean_inc(v_name_1254_);
lean_dec_ref(v_info_1244_);
v___x_1255_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
v___x_1256_ = 1;
v___x_1257_ = l_Lean_Name_toString(v_name_1254_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 5);
lean_ctor_set(v___x_1247_, 1, v___x_1258_);
lean_ctor_set(v___x_1247_, 0, v___x_1255_);
v___x_1260_ = v___x_1247_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1261_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Std_Format_indentD(v_a_1250_);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1264_);
v___x_1266_ = v___x_1252_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_del_object(v___x_1247_);
lean_dec_ref(v_info_1244_);
return v___x_1249_;
}
}
}
default: 
{
lean_object* v_code_1271_; lean_object* v___x_1272_; 
v_code_1271_ = lean_ctor_get(v_alt_1207_, 0);
lean_inc_ref(v_code_1271_);
lean_dec_ref(v_alt_1207_);
v___x_1272_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1206_, v_code_1271_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1283_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1283_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1283_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1277_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
v___x_1278_ = l_Std_Format_indentD(v_a_1273_);
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1279_);
v___x_1281_ = v___x_1275_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* v_pu_1284_, lean_object* v_alt_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
uint8_t v_pu_boxed_1292_; lean_object* v_res_1293_; 
v_pu_boxed_1292_ = lean_unbox(v_pu_1284_);
v_res_1293_ = l_Lean_Compiler_LCNF_PP_ppAlt(v_pu_boxed_1292_, v_alt_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec_ref(v_a_1286_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t v_pu_1342_, lean_object* v_c_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
switch(lean_obj_tag(v_c_1343_))
{
case 0:
{
lean_object* v_decl_1350_; lean_object* v_k_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1373_; 
v_decl_1350_ = lean_ctor_get(v_c_1343_, 0);
v_k_1351_ = lean_ctor_get(v_c_1343_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1353_ = v_c_1343_;
v_isShared_1354_ = v_isSharedCheck_1373_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_k_1351_);
lean_inc(v_decl_1350_);
lean_dec(v_c_1343_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1373_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(v_pu_1342_, v_decl_1350_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1351_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1372_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 5);
lean_ctor_set(v___x_1353_, 1, v___x_1362_);
lean_ctor_set(v___x_1353_, 0, v_a_1356_);
v___x_1364_ = v___x_1353_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1365_ = lean_box(1);
v___x_1366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v_a_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1367_);
v___x_1369_ = v___x_1360_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_dec(v_a_1356_);
lean_del_object(v___x_1353_);
return v___x_1357_;
}
}
else
{
lean_del_object(v___x_1353_);
lean_dec_ref(v_k_1351_);
return v___x_1355_;
}
}
}
case 1:
{
lean_object* v_decl_1374_; lean_object* v_k_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1399_; 
v_decl_1374_ = lean_ctor_get(v_c_1343_, 0);
v_k_1375_ = lean_ctor_get(v_c_1343_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1377_ = v_c_1343_;
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_k_1375_);
lean_inc(v_decl_1374_);
lean_dec(v_c_1343_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1342_, v_decl_1374_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1375_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1398_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1398_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1398_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 5);
lean_ctor_set(v___x_1377_, 1, v_a_1380_);
lean_ctor_set(v___x_1377_, 0, v___x_1386_);
v___x_1388_ = v___x_1377_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_a_1380_);
v___x_1388_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1389_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_box(1);
v___x_1392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v_a_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1393_);
v___x_1395_ = v___x_1384_;
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
lean_dec(v_a_1380_);
lean_del_object(v___x_1377_);
return v___x_1381_;
}
}
else
{
lean_del_object(v___x_1377_);
lean_dec_ref(v_k_1375_);
return v___x_1379_;
}
}
}
case 2:
{
lean_object* v_decl_1400_; lean_object* v_k_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_decl_1400_ = lean_ctor_get(v_c_1343_, 0);
v_k_1401_ = lean_ctor_get(v_c_1343_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v_c_1343_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_k_1401_);
lean_inc(v_decl_1400_);
lean_dec(v_c_1343_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_1342_, v_decl_1400_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1401_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
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
v___x_1412_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
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
case 3:
{
lean_object* v_fvarId_1426_; lean_object* v_args_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1447_; 
v_fvarId_1426_ = lean_ctor_get(v_c_1343_, 0);
v_args_1427_ = lean_ctor_get(v_c_1343_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1429_ = v_c_1343_;
v_isShared_1430_ = v_isSharedCheck_1447_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_args_1427_);
lean_inc(v_fvarId_1426_);
lean_dec(v_c_1343_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1447_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1426_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = l_Lean_Compiler_LCNF_PP_ppArgs(v_pu_1342_, v_args_1427_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec_ref(v_args_1427_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
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
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_a_1432_);
v___x_1440_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v_a_1434_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1441_);
v___x_1443_ = v___x_1436_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
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
lean_dec_ref(v_args_1427_);
return v___x_1431_;
}
}
}
case 4:
{
lean_object* v_cases_1448_; lean_object* v_resultType_1449_; lean_object* v_discr_1450_; lean_object* v_alts_1451_; lean_object* v___x_1452_; 
v_cases_1448_ = lean_ctor_get(v_c_1343_, 0);
lean_inc_ref(v_cases_1448_);
lean_dec_ref(v_c_1343_);
v_resultType_1449_ = lean_ctor_get(v_cases_1448_, 1);
lean_inc_ref(v_resultType_1449_);
v_discr_1450_ = lean_ctor_get(v_cases_1448_, 2);
lean_inc(v_discr_1450_);
v_alts_1451_ = lean_ctor_get(v_cases_1448_, 3);
lean_inc_ref(v_alts_1451_);
lean_dec_ref(v_cases_1448_);
v___x_1452_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_discr_1450_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_resultType_1449_, v_a_1344_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = lean_box(1);
v___x_1457_ = lean_box(v_pu_1342_);
v___x_1458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(v___x_1458_, 0, v___x_1457_);
v___x_1459_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_1456_, v_alts_1451_, v___x_1458_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec_ref(v_alts_1451_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1473_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1464_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
v___x_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v_a_1453_);
v___x_1466_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v_a_1455_);
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_a_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1469_);
v___x_1471_ = v___x_1462_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
else
{
lean_dec(v_a_1455_);
lean_dec(v_a_1453_);
return v___x_1459_;
}
}
else
{
lean_dec(v_a_1453_);
lean_dec_ref(v_alts_1451_);
return v___x_1454_;
}
}
else
{
lean_dec_ref(v_alts_1451_);
lean_dec_ref(v_resultType_1449_);
return v___x_1452_;
}
}
case 5:
{
lean_object* v_fvarId_1474_; lean_object* v___x_1475_; 
v_fvarId_1474_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1474_);
lean_dec_ref(v_c_1343_);
v___x_1475_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1474_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
v___x_1481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_a_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
return v___x_1475_;
}
}
case 6:
{
lean_object* v_type_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1508_; 
v_type_1486_ = lean_ctor_get(v_c_1343_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1488_ = v_c_1343_;
v_isShared_1489_ = v_isSharedCheck_1508_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_type_1486_);
lean_dec(v_c_1343_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1508_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_options_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_options_1490_ = lean_ctor_get(v_a_1347_, 2);
v___x_1491_ = l_Lean_pp_all;
v___x_1492_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec_ref(v_type_1486_);
v___x_1493_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1493_);
v___x_1495_ = v___x_1488_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_object* v___x_1497_; 
lean_del_object(v___x_1488_);
v___x_1497_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_type_1486_, v_a_1344_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1507_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1502_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
v___x_1503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v_a_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
return v___x_1497_;
}
}
}
}
case 7:
{
lean_object* v_fvarId_1509_; lean_object* v_i_1510_; lean_object* v_y_1511_; lean_object* v_k_1512_; lean_object* v___x_1513_; 
v_fvarId_1509_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1509_);
v_i_1510_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_i_1510_);
v_y_1511_ = lean_ctor_get(v_c_1343_, 2);
lean_inc(v_y_1511_);
v_k_1512_ = lean_ctor_get(v_c_1343_, 3);
lean_inc_ref(v_k_1512_);
lean_dec_ref(v_c_1343_);
v___x_1513_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1509_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(v_y_1511_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1546_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1512_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1525_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_a_1514_);
v___x_1527_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Nat_reprFast(v_i_1510_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 3);
lean_ctor_set(v___x_1518_, 0, v___x_1529_);
v___x_1531_ = v___x_1518_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1528_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_a_1516_);
v___x_1536_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_box(1);
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1540_);
v___x_1542_ = v___x_1523_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_del_object(v___x_1518_);
lean_dec(v_a_1516_);
lean_dec(v_a_1514_);
lean_dec(v_i_1510_);
return v___x_1520_;
}
}
}
else
{
lean_dec(v_a_1514_);
lean_dec_ref(v_k_1512_);
lean_dec(v_i_1510_);
return v___x_1515_;
}
}
else
{
lean_dec_ref(v_k_1512_);
lean_dec(v_y_1511_);
lean_dec(v_i_1510_);
return v___x_1513_;
}
}
case 8:
{
lean_object* v_fvarId_1547_; lean_object* v_i_1548_; lean_object* v_y_1549_; lean_object* v_k_1550_; lean_object* v___x_1551_; 
v_fvarId_1547_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1547_);
v_i_1548_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_i_1548_);
v_y_1549_ = lean_ctor_get(v_c_1343_, 2);
lean_inc(v_y_1549_);
v_k_1550_ = lean_ctor_get(v_c_1343_, 3);
lean_inc_ref(v_k_1550_);
lean_dec_ref(v_c_1343_);
v___x_1551_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1547_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1549_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1584_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1584_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1584_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1550_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1583_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1583_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1583_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1563_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1552_);
v___x_1565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Nat_reprFast(v_i_1548_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 3);
lean_ctor_set(v___x_1556_, 0, v___x_1567_);
v___x_1569_ = v___x_1556_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1566_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_a_1554_);
v___x_1574_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_box(1);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1578_);
v___x_1580_ = v___x_1561_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_del_object(v___x_1556_);
lean_dec(v_a_1554_);
lean_dec(v_a_1552_);
lean_dec(v_i_1548_);
return v___x_1558_;
}
}
}
else
{
lean_dec(v_a_1552_);
lean_dec_ref(v_k_1550_);
lean_dec(v_i_1548_);
return v___x_1553_;
}
}
else
{
lean_dec_ref(v_k_1550_);
lean_dec(v_y_1549_);
lean_dec(v_i_1548_);
return v___x_1551_;
}
}
case 9:
{
lean_object* v_fvarId_1585_; lean_object* v_i_1586_; lean_object* v_offset_1587_; lean_object* v_y_1588_; lean_object* v_ty_1589_; lean_object* v_k_1590_; lean_object* v_options_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_fvarId_1585_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1585_);
v_i_1586_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_i_1586_);
v_offset_1587_ = lean_ctor_get(v_c_1343_, 2);
lean_inc(v_offset_1587_);
v_y_1588_ = lean_ctor_get(v_c_1343_, 3);
lean_inc(v_y_1588_);
v_ty_1589_ = lean_ctor_get(v_c_1343_, 4);
lean_inc_ref(v_ty_1589_);
v_k_1590_ = lean_ctor_get(v_c_1343_, 5);
lean_inc_ref(v_k_1590_);
lean_dec_ref(v_c_1343_);
v_options_1591_ = lean_ctor_get(v_a_1347_, 2);
v___x_1592_ = l_Lean_pp_letVarTypes;
v___x_1593_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_options_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref(v_ty_1589_);
v___x_1594_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1585_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1638_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1638_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1638_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1588_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1637_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1637_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1637_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1590_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1636_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1636_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1636_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1609_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1595_);
v___x_1611_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Nat_reprFast(v_i_1586_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 3);
lean_ctor_set(v___x_1602_, 0, v___x_1613_);
v___x_1615_ = v___x_1602_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1612_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = l_Nat_reprFast(v_offset_1587_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 3);
lean_ctor_set(v___x_1597_, 0, v___x_1619_);
v___x_1621_ = v___x_1597_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1618_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
v___x_1624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_a_1600_);
v___x_1626_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_box(1);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1630_);
v___x_1632_ = v___x_1607_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_del_object(v___x_1602_);
lean_dec(v_a_1600_);
lean_del_object(v___x_1597_);
lean_dec(v_a_1595_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1604_;
}
}
}
else
{
lean_del_object(v___x_1597_);
lean_dec(v_a_1595_);
lean_dec_ref(v_k_1590_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1599_;
}
}
}
else
{
lean_dec_ref(v_k_1590_);
lean_dec(v_y_1588_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1594_;
}
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1585_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_ty_1589_, v_a_1344_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1688_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1688_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1688_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_y_1588_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1687_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1687_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1687_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1590_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1686_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1686_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1686_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1656_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
v___x_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v_a_1640_);
v___x_1658_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Nat_reprFast(v_i_1586_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 3);
lean_ctor_set(v___x_1649_, 0, v___x_1660_);
v___x_1662_ = v___x_1649_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1659_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
v___x_1665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Nat_reprFast(v_offset_1587_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 3);
lean_ctor_set(v___x_1644_, 0, v___x_1666_);
v___x_1668_ = v___x_1644_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1665_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__27));
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_a_1642_);
v___x_1673_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1647_);
v___x_1676_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_box(1);
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_a_1652_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1680_);
v___x_1682_ = v___x_1654_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
else
{
lean_del_object(v___x_1649_);
lean_dec(v_a_1647_);
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_dec(v_a_1640_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1651_;
}
}
}
else
{
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_dec(v_a_1640_);
lean_dec_ref(v_k_1590_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1646_;
}
}
}
else
{
lean_dec(v_a_1640_);
lean_dec_ref(v_k_1590_);
lean_dec(v_y_1588_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1641_;
}
}
else
{
lean_dec_ref(v_k_1590_);
lean_dec_ref(v_ty_1589_);
lean_dec(v_y_1588_);
lean_dec(v_offset_1587_);
lean_dec(v_i_1586_);
return v___x_1639_;
}
}
}
case 10:
{
lean_object* v_fvarId_1689_; lean_object* v_cidx_1690_; lean_object* v_k_1691_; lean_object* v___x_1692_; 
v_fvarId_1689_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1689_);
v_cidx_1690_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_cidx_1690_);
v_k_1691_ = lean_ctor_get(v_c_1343_, 2);
lean_inc_ref(v_k_1691_);
lean_dec_ref(v_c_1343_);
v___x_1692_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1689_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1720_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1720_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1720_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1691_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1719_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1719_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1719_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1702_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__29));
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_a_1693_);
v___x_1704_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Nat_reprFast(v_cidx_1690_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 3);
lean_ctor_set(v___x_1695_, 0, v___x_1706_);
v___x_1708_ = v___x_1695_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1705_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_box(1);
v___x_1713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1714_);
v___x_1716_ = v___x_1700_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_del_object(v___x_1695_);
lean_dec(v_a_1693_);
lean_dec(v_cidx_1690_);
return v___x_1697_;
}
}
}
else
{
lean_dec_ref(v_k_1691_);
lean_dec(v_cidx_1690_);
return v___x_1692_;
}
}
case 11:
{
lean_object* v_fvarId_1721_; lean_object* v_n_1722_; lean_object* v_k_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_fvarId_1721_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1721_);
v_n_1722_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_n_1722_);
v_k_1723_ = lean_ctor_get(v_c_1343_, 2);
lean_inc_ref(v_k_1723_);
lean_dec_ref(v_c_1343_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_dec_eq(v_n_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1721_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1754_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1754_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1754_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1723_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1753_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1753_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1753_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__31));
v___x_1737_ = l_Nat_reprFast(v_n_1722_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 3);
lean_ctor_set(v___x_1729_, 0, v___x_1737_);
v___x_1739_ = v___x_1729_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1736_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_1742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1727_);
v___x_1744_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_box(1);
v___x_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_a_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1748_);
v___x_1750_ = v___x_1734_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_del_object(v___x_1729_);
lean_dec(v_a_1727_);
lean_dec(v_n_1722_);
return v___x_1731_;
}
}
}
else
{
lean_dec_ref(v_k_1723_);
lean_dec(v_n_1722_);
return v___x_1726_;
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_n_1722_);
v___x_1755_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1721_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1723_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1772_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1772_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1772_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1762_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__33));
v___x_1763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1756_);
v___x_1764_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_box(1);
v___x_1767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1768_);
v___x_1770_ = v___x_1760_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_dec(v_a_1756_);
return v___x_1757_;
}
}
else
{
lean_dec_ref(v_k_1723_);
return v___x_1755_;
}
}
}
case 12:
{
lean_object* v_fvarId_1773_; lean_object* v_n_1774_; lean_object* v_k_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_fvarId_1773_ = lean_ctor_get(v_c_1343_, 0);
lean_inc(v_fvarId_1773_);
v_n_1774_ = lean_ctor_get(v_c_1343_, 1);
lean_inc(v_n_1774_);
v_k_1775_ = lean_ctor_get(v_c_1343_, 2);
lean_inc_ref(v_k_1775_);
lean_dec_ref(v_c_1343_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_dec_eq(v_n_1774_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1773_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1806_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1806_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1806_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1775_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1805_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1805_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1805_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1788_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__35));
v___x_1789_ = l_Nat_reprFast(v_n_1774_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 3);
lean_ctor_set(v___x_1781_, 0, v___x_1789_);
v___x_1791_ = v___x_1781_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1788_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
v___x_1794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_a_1779_);
v___x_1796_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_box(1);
v___x_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1800_);
v___x_1802_ = v___x_1786_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_del_object(v___x_1781_);
lean_dec(v_a_1779_);
lean_dec(v_n_1774_);
return v___x_1783_;
}
}
}
else
{
lean_dec_ref(v_k_1775_);
lean_dec(v_n_1774_);
return v___x_1778_;
}
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_n_1774_);
v___x_1807_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1773_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1775_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1824_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1824_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1824_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1814_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__37));
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_a_1808_);
v___x_1816_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
v___x_1817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_box(1);
v___x_1819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_a_1810_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1820_);
v___x_1822_ = v___x_1812_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_dec(v_a_1808_);
return v___x_1809_;
}
}
else
{
lean_dec_ref(v_k_1775_);
return v___x_1807_;
}
}
}
default: 
{
lean_object* v_fvarId_1825_; lean_object* v_k_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1850_; 
v_fvarId_1825_ = lean_ctor_get(v_c_1343_, 0);
v_k_1826_ = lean_ctor_get(v_c_1343_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_c_1343_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1828_ = v_c_1343_;
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_k_1826_);
lean_inc(v_fvarId_1825_);
lean_dec(v_c_1343_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_fvarId_1825_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1342_, v_k_1826_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1849_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__39));
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 5);
lean_ctor_set(v___x_1828_, 1, v_a_1831_);
lean_ctor_set(v___x_1828_, 0, v___x_1837_);
v___x_1839_ = v___x_1828_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_a_1831_);
v___x_1839_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
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
lean_ctor_set(v___x_1844_, 1, v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1844_);
v___x_1846_ = v___x_1835_;
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
lean_dec(v_a_1831_);
lean_del_object(v___x_1828_);
return v___x_1832_;
}
}
else
{
lean_del_object(v___x_1828_);
lean_dec_ref(v_k_1826_);
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t v_pu_1851_, lean_object* v_funDecl_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v_binderName_1859_; lean_object* v_params_1860_; lean_object* v_type_1861_; lean_object* v_value_1862_; lean_object* v___x_1863_; 
v_binderName_1859_ = lean_ctor_get(v_funDecl_1852_, 1);
lean_inc(v_binderName_1859_);
v_params_1860_ = lean_ctor_get(v_funDecl_1852_, 2);
lean_inc_ref(v_params_1860_);
v_type_1861_ = lean_ctor_get(v_funDecl_1852_, 3);
lean_inc_ref(v_type_1861_);
v_value_1862_ = lean_ctor_get(v_funDecl_1852_, 4);
lean_inc_ref(v_value_1862_);
lean_dec_ref(v_funDecl_1852_);
v___x_1863_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_1851_, v_params_1860_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_1851_, v_params_1860_, v_type_1861_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_1866_, v_a_1853_, v_a_1856_, v_a_1857_);
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
v___x_1872_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1851_, v_value_1862_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
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
uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = 1;
v___x_1878_ = l_Lean_Name_toString(v_binderName_1859_, v___x_1877_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 3);
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_a_1864_);
v___x_1882_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v_a_1868_);
v___x_1885_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_1886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Std_Format_indentD(v_a_1873_);
v___x_1888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
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
lean_dec(v_a_1864_);
lean_dec(v_binderName_1859_);
return v___x_1872_;
}
}
}
else
{
lean_dec(v_a_1864_);
lean_dec_ref(v_value_1862_);
lean_dec(v_binderName_1859_);
return v___x_1867_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1864_);
lean_dec_ref(v_value_1862_);
lean_dec(v_binderName_1859_);
v_a_1895_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1865_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1865_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_dec_ref(v_value_1862_);
lean_dec_ref(v_type_1861_);
lean_dec_ref(v_params_1860_);
lean_dec(v_binderName_1859_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* v_pu_1903_, lean_object* v_funDecl_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
uint8_t v_pu_boxed_1911_; lean_object* v_res_1912_; 
v_pu_boxed_1911_ = lean_unbox(v_pu_1903_);
v_res_1912_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_boxed_1911_, v_funDecl_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec_ref(v_a_1905_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* v_pu_1913_, lean_object* v_c_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
uint8_t v_pu_boxed_1921_; lean_object* v_res_1922_; 
v_pu_boxed_1921_ = lean_unbox(v_pu_1913_);
v_res_1922_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_boxed_1921_, v_c_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec_ref(v_a_1915_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t v_pu_1926_, lean_object* v_b_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
if (lean_obj_tag(v_b_1927_) == 0)
{
lean_object* v_code_1934_; lean_object* v___x_1935_; 
v_code_1934_ = lean_ctor_get(v_b_1927_, 0);
lean_inc_ref(v_code_1934_);
lean_dec_ref(v_b_1927_);
v___x_1935_ = l_Lean_Compiler_LCNF_PP_ppCode(v_pu_1926_, v_code_1934_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
return v___x_1935_;
}
else
{
lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
v_isSharedCheck_1943_ = !lean_is_exclusive(v_b_1927_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_b_1927_, 0);
lean_dec(v_unused_1944_);
v___x_1937_ = v_b_1927_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_dec(v_b_1927_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1939_);
v___x_1941_ = v___x_1937_;
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* v_pu_1945_, lean_object* v_b_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
uint8_t v_pu_boxed_1953_; lean_object* v_res_1954_; 
v_pu_boxed_1953_ = lean_unbox(v_pu_1945_);
v_res_1954_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_boxed_1953_, v_b_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec_ref(v_a_1947_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* v_opts_1955_, lean_object* v_opt_1956_){
_start:
{
lean_object* v_name_1957_; lean_object* v_defValue_1958_; lean_object* v_map_1959_; lean_object* v___x_1960_; 
v_name_1957_ = lean_ctor_get(v_opt_1956_, 0);
v_defValue_1958_ = lean_ctor_get(v_opt_1956_, 1);
v_map_1959_ = lean_ctor_get(v_opts_1955_, 0);
v___x_1960_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1959_, v_name_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_inc(v_defValue_1958_);
return v_defValue_1958_;
}
else
{
lean_object* v_val_1961_; 
v_val_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_val_1961_);
lean_dec_ref(v___x_1960_);
if (lean_obj_tag(v_val_1961_) == 3)
{
lean_object* v_v_1962_; 
v_v_1962_ = lean_ctor_get(v_val_1961_, 0);
lean_inc(v_v_1962_);
lean_dec_ref(v_val_1961_);
return v_v_1962_;
}
else
{
lean_dec(v_val_1961_);
lean_inc(v_defValue_1958_);
return v_defValue_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* v_opts_1963_, lean_object* v_opt_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_1963_, v_opt_1964_);
lean_dec_ref(v_opt_1964_);
lean_dec_ref(v_opts_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(lean_object* v_o_1969_, lean_object* v_k_1970_, uint8_t v_v_1971_){
_start:
{
lean_object* v_map_1972_; uint8_t v_hasTrace_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1987_; 
v_map_1972_ = lean_ctor_get(v_o_1969_, 0);
v_hasTrace_1973_ = lean_ctor_get_uint8(v_o_1969_, sizeof(void*)*1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_o_1969_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1975_ = v_o_1969_;
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_map_1972_);
lean_dec(v_o_1969_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1977_, 0, v_v_1971_);
lean_inc(v_k_1970_);
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1970_, v___x_1977_, v_map_1972_);
if (v_hasTrace_1973_ == 0)
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1));
v___x_1980_ = l_Lean_Name_isPrefixOf(v___x_1979_, v_k_1970_);
lean_dec(v_k_1970_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1978_);
v___x_1982_ = v___x_1975_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1978_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*1, v___x_1980_);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1985_; 
lean_dec(v_k_1970_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1978_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*1, v_hasTrace_1973_);
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
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(lean_object* v_o_1988_, lean_object* v_k_1989_, lean_object* v_v_1990_){
_start:
{
uint8_t v_v_boxed_1991_; lean_object* v_res_1992_; 
v_v_boxed_1991_ = lean_unbox(v_v_1990_);
v_res_1992_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_o_1988_, v_k_1989_, v_v_boxed_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* v_opts_1993_, lean_object* v_opt_1994_, uint8_t v_val_1995_){
_start:
{
lean_object* v_name_1996_; lean_object* v___x_1997_; 
v_name_1996_ = lean_ctor_get(v_opt_1994_, 0);
lean_inc(v_name_1996_);
lean_dec_ref(v_opt_1994_);
v___x_1997_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_opts_1993_, v_name_1996_, v_val_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* v_opts_1998_, lean_object* v_opt_1999_, lean_object* v_val_2000_){
_start:
{
uint8_t v_val_boxed_2001_; lean_object* v_res_2002_; 
v_val_boxed_2001_ = lean_unbox(v_val_2000_);
v_res_2002_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_opts_1998_, v_opt_1999_, v_val_boxed_2001_);
return v_res_2002_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__0, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__1, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v_options_2015_; lean_object* v_env_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2057_; uint8_t v___x_2078_; 
v___x_2014_ = lean_st_ref_get(v_a_2012_);
v_options_2015_ = lean_ctor_get(v_a_2011_, 2);
v_env_2016_ = lean_ctor_get(v___x_2014_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2014_);
v___x_2017_ = l_Lean_pp_sanitizeNames;
v___x_2018_ = 0;
lean_inc_ref(v_options_2015_);
v___x_2019_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(v_options_2015_, v___x_2017_, v___x_2018_);
v___x_2020_ = l_Lean_diagnostics;
v___x_2021_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v___x_2019_, v___x_2020_);
v___x_2078_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2016_);
lean_dec_ref(v_env_2016_);
if (v___x_2078_ == 0)
{
if (v___x_2021_ == 0)
{
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
goto v___jp_2022_;
}
else
{
v___y_2057_ = v___x_2078_;
goto v___jp_2056_;
}
}
else
{
v___y_2057_ = v___x_2021_;
goto v___jp_2056_;
}
v___jp_2022_:
{
lean_object* v___x_2025_; lean_object* v_fileName_2026_; lean_object* v_fileMap_2027_; lean_object* v_currRecDepth_2028_; lean_object* v_ref_2029_; lean_object* v_currNamespace_2030_; lean_object* v_openDecls_2031_; lean_object* v_initHeartbeats_2032_; lean_object* v_maxHeartbeats_2033_; lean_object* v_quotContext_2034_; lean_object* v_currMacroScope_2035_; lean_object* v_cancelTk_x3f_2036_; uint8_t v_suppressElabErrors_2037_; lean_object* v_inheritedTraceOptions_2038_; lean_object* v___x_2039_; 
v___x_2025_ = lean_st_ref_get(v_a_2010_);
v_fileName_2026_ = lean_ctor_get(v___y_2023_, 0);
lean_inc_ref(v_fileName_2026_);
v_fileMap_2027_ = lean_ctor_get(v___y_2023_, 1);
lean_inc_ref(v_fileMap_2027_);
v_currRecDepth_2028_ = lean_ctor_get(v___y_2023_, 3);
lean_inc(v_currRecDepth_2028_);
v_ref_2029_ = lean_ctor_get(v___y_2023_, 5);
lean_inc(v_ref_2029_);
v_currNamespace_2030_ = lean_ctor_get(v___y_2023_, 6);
lean_inc(v_currNamespace_2030_);
v_openDecls_2031_ = lean_ctor_get(v___y_2023_, 7);
lean_inc(v_openDecls_2031_);
v_initHeartbeats_2032_ = lean_ctor_get(v___y_2023_, 8);
lean_inc(v_initHeartbeats_2032_);
v_maxHeartbeats_2033_ = lean_ctor_get(v___y_2023_, 9);
lean_inc(v_maxHeartbeats_2033_);
v_quotContext_2034_ = lean_ctor_get(v___y_2023_, 10);
lean_inc(v_quotContext_2034_);
v_currMacroScope_2035_ = lean_ctor_get(v___y_2023_, 11);
lean_inc(v_currMacroScope_2035_);
v_cancelTk_x3f_2036_ = lean_ctor_get(v___y_2023_, 12);
lean_inc(v_cancelTk_x3f_2036_);
v_suppressElabErrors_2037_ = lean_ctor_get_uint8(v___y_2023_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2038_ = lean_ctor_get(v___y_2023_, 13);
lean_inc_ref(v_inheritedTraceOptions_2038_);
lean_dec_ref(v___y_2023_);
v___x_2039_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_2009_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v_lctx_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
v_lctx_2041_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_ref(v_lctx_2041_);
lean_dec(v___x_2025_);
v___x_2042_ = l_Lean_maxRecDepth;
v___x_2043_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v___x_2019_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2044_, 0, v_fileName_2026_);
lean_ctor_set(v___x_2044_, 1, v_fileMap_2027_);
lean_ctor_set(v___x_2044_, 2, v___x_2019_);
lean_ctor_set(v___x_2044_, 3, v_currRecDepth_2028_);
lean_ctor_set(v___x_2044_, 4, v___x_2043_);
lean_ctor_set(v___x_2044_, 5, v_ref_2029_);
lean_ctor_set(v___x_2044_, 6, v_currNamespace_2030_);
lean_ctor_set(v___x_2044_, 7, v_openDecls_2031_);
lean_ctor_set(v___x_2044_, 8, v_initHeartbeats_2032_);
lean_ctor_set(v___x_2044_, 9, v_maxHeartbeats_2033_);
lean_ctor_set(v___x_2044_, 10, v_quotContext_2034_);
lean_ctor_set(v___x_2044_, 11, v_currMacroScope_2035_);
lean_ctor_set(v___x_2044_, 12, v_cancelTk_x3f_2036_);
lean_ctor_set(v___x_2044_, 13, v_inheritedTraceOptions_2038_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*14, v___x_2021_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*14 + 1, v_suppressElabErrors_2037_);
v___x_2045_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
v___x_2046_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2041_, v___x_2045_);
lean_dec_ref(v_lctx_2041_);
lean_inc(v___y_2024_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
v___x_2047_ = lean_apply_6(v_x_2008_, v___x_2046_, v_a_2009_, v_a_2010_, v___x_2044_, v___y_2024_, lean_box(0));
return v___x_2047_;
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_inheritedTraceOptions_2038_);
lean_dec(v_cancelTk_x3f_2036_);
lean_dec(v_currMacroScope_2035_);
lean_dec(v_quotContext_2034_);
lean_dec(v_maxHeartbeats_2033_);
lean_dec(v_initHeartbeats_2032_);
lean_dec(v_openDecls_2031_);
lean_dec(v_currNamespace_2030_);
lean_dec(v_ref_2029_);
lean_dec(v_currRecDepth_2028_);
lean_dec_ref(v_fileMap_2027_);
lean_dec_ref(v_fileName_2026_);
lean_dec(v___x_2025_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_x_2008_);
v_a_2048_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2039_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2039_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
v___jp_2056_:
{
if (v___y_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v_env_2059_; lean_object* v_nextMacroScope_2060_; lean_object* v_ngen_2061_; lean_object* v_auxDeclNGen_2062_; lean_object* v_traceState_2063_; lean_object* v_messages_2064_; lean_object* v_infoState_2065_; lean_object* v_snapshotTasks_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2076_; 
v___x_2058_ = lean_st_ref_take(v_a_2012_);
v_env_2059_ = lean_ctor_get(v___x_2058_, 0);
v_nextMacroScope_2060_ = lean_ctor_get(v___x_2058_, 1);
v_ngen_2061_ = lean_ctor_get(v___x_2058_, 2);
v_auxDeclNGen_2062_ = lean_ctor_get(v___x_2058_, 3);
v_traceState_2063_ = lean_ctor_get(v___x_2058_, 4);
v_messages_2064_ = lean_ctor_get(v___x_2058_, 6);
v_infoState_2065_ = lean_ctor_get(v___x_2058_, 7);
v_snapshotTasks_2066_ = lean_ctor_get(v___x_2058_, 8);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v___x_2058_, 5);
lean_dec(v_unused_2077_);
v___x_2068_ = v___x_2058_;
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_snapshotTasks_2066_);
lean_inc(v_infoState_2065_);
lean_inc(v_messages_2064_);
lean_inc(v_traceState_2063_);
lean_inc(v_auxDeclNGen_2062_);
lean_inc(v_ngen_2061_);
lean_inc(v_nextMacroScope_2060_);
lean_inc(v_env_2059_);
lean_dec(v___x_2058_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2070_ = l_Lean_Kernel_enableDiag(v_env_2059_, v___x_2021_);
v___x_2071_ = lean_obj_once(&l_Lean_Compiler_LCNF_PP_run___redArg___closed__2, &l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 5, v___x_2071_);
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2073_ = v___x_2068_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_nextMacroScope_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_ngen_2061_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_auxDeclNGen_2062_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_traceState_2063_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2075_, 6, v_messages_2064_);
lean_ctor_set(v_reuseFailAlloc_2075_, 7, v_infoState_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 8, v_snapshotTasks_2066_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_st_ref_set(v_a_2012_, v___x_2073_);
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
goto v___jp_2022_;
}
}
}
else
{
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
goto v___jp_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* v_x_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* v_00_u03b1_2086_, lean_object* v_x_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; 
lean_inc_ref(v_a_2090_);
v___x_2093_ = l_Lean_Compiler_LCNF_PP_run___redArg(v_x_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_x_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Compiler_LCNF_PP_run(v_00_u03b1_2094_, v_x_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t v_pu_2102_, lean_object* v_code_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = lean_box(v_pu_2102_);
v___x_2110_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(v___x_2110_, 0, v___x_2109_);
lean_closure_set(v___x_2110_, 1, v_code_2103_);
lean_inc_ref(v_a_2106_);
v___x_2111_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2110_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* v_pu_2112_, lean_object* v_code_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v_pu_boxed_2119_; lean_object* v_res_2120_; 
v_pu_boxed_2119_ = lean_unbox(v_pu_2112_);
v_res_2120_ = l_Lean_Compiler_LCNF_ppCode(v_pu_boxed_2119_, v_code_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t v_pu_2121_, lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_box(v_pu_2121_);
v___x_2129_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(v___x_2129_, 0, v___x_2128_);
lean_closure_set(v___x_2129_, 1, v_e_2122_);
lean_inc_ref(v_a_2125_);
v___x_2130_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2129_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* v_pu_2131_, lean_object* v_e_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
uint8_t v_pu_boxed_2138_; lean_object* v_res_2139_; 
v_pu_boxed_2138_ = lean_unbox(v_pu_2131_);
v_res_2139_ = l_Lean_Compiler_LCNF_ppLetValue(v_pu_boxed_2138_, v_e_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t v_pu_2143_, lean_object* v_params_2144_, lean_object* v_type_2145_, lean_object* v_value_2146_, lean_object* v_name_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Compiler_LCNF_PP_ppParams(v_pu_2143_, v_params_2144_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = l_Lean_Compiler_LCNF_PP_getFunType(v_pu_2143_, v_params_2144_, v_type_2145_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_a_2157_, v___y_2148_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2187_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2187_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2187_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(v_pu_2143_, v_value_2146_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2186_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2186_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2186_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2168_ = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
v___x_2169_ = 1;
v___x_2170_ = l_Lean_Name_toString(v_name_2147_, v___x_2169_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 3);
lean_ctor_set(v___x_2161_, 0, v___x_2170_);
v___x_2172_ = v___x_2161_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2168_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_a_2155_);
v___x_2175_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
v___x_2176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v_a_2159_);
v___x_2178_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
v___x_2179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = l_Std_Format_indentD(v_a_2164_);
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2181_);
v___x_2183_ = v___x_2166_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_del_object(v___x_2161_);
lean_dec(v_a_2159_);
lean_dec(v_a_2155_);
lean_dec(v_name_2147_);
return v___x_2163_;
}
}
}
else
{
lean_dec(v_a_2155_);
lean_dec(v_name_2147_);
lean_dec_ref(v_value_2146_);
return v___x_2158_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2155_);
lean_dec(v_name_2147_);
lean_dec_ref(v_value_2146_);
v_a_2188_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2156_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2156_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_dec(v_name_2147_);
lean_dec_ref(v_value_2146_);
lean_dec_ref(v_type_2145_);
lean_dec_ref(v_params_2144_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* v_pu_2196_, lean_object* v_params_2197_, lean_object* v_type_2198_, lean_object* v_value_2199_, lean_object* v_name_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v_pu_boxed_2207_; lean_object* v_res_2208_; 
v_pu_boxed_2207_ = lean_unbox(v_pu_2196_);
v_res_2208_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(v_pu_boxed_2207_, v_params_2197_, v_type_2198_, v_value_2199_, v_name_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t v_pu_2209_, lean_object* v_decl_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_toSignature_2216_; lean_object* v_value_2217_; lean_object* v_name_2218_; lean_object* v_type_2219_; lean_object* v_params_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; 
v_toSignature_2216_ = lean_ctor_get(v_decl_2210_, 0);
lean_inc_ref(v_toSignature_2216_);
v_value_2217_ = lean_ctor_get(v_decl_2210_, 1);
lean_inc_ref(v_value_2217_);
lean_dec_ref(v_decl_2210_);
v_name_2218_ = lean_ctor_get(v_toSignature_2216_, 0);
lean_inc(v_name_2218_);
v_type_2219_ = lean_ctor_get(v_toSignature_2216_, 2);
lean_inc_ref(v_type_2219_);
v_params_2220_ = lean_ctor_get(v_toSignature_2216_, 3);
lean_inc_ref(v_params_2220_);
lean_dec_ref(v_toSignature_2216_);
v___x_2221_ = lean_box(v_pu_2209_);
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2222_, 0, v___x_2221_);
lean_closure_set(v___f_2222_, 1, v_params_2220_);
lean_closure_set(v___f_2222_, 2, v_type_2219_);
lean_closure_set(v___f_2222_, 3, v_value_2217_);
lean_closure_set(v___f_2222_, 4, v_name_2218_);
lean_inc_ref(v_a_2213_);
v___x_2223_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2222_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* v_pu_2224_, lean_object* v_decl_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
uint8_t v_pu_boxed_2231_; lean_object* v_res_2232_; 
v_pu_boxed_2231_ = lean_unbox(v_pu_2224_);
v_res_2232_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_boxed_2231_, v_decl_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t v_pu_2233_, lean_object* v_decl_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(v_pu_2233_, v_decl_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2251_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2247_);
v___x_2249_ = v___x_2244_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* v_pu_2252_, lean_object* v_decl_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_pu_boxed_2260_; lean_object* v_res_2261_; 
v_pu_boxed_2260_ = lean_unbox(v_pu_2252_);
v_res_2261_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(v_pu_boxed_2260_, v_decl_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t v_pu_2262_, lean_object* v_decl_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_box(v_pu_2262_);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
lean_closure_set(v___f_2270_, 1, v_decl_2263_);
lean_inc_ref(v_a_2266_);
v___x_2271_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___f_2270_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* v_pu_2272_, lean_object* v_decl_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
uint8_t v_pu_boxed_2279_; lean_object* v_res_2280_; 
v_pu_boxed_2279_ = lean_unbox(v_pu_2272_);
v_res_2280_ = l_Lean_Compiler_LCNF_ppFunDecl(v_pu_boxed_2279_, v_decl_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* v_a_2281_, lean_object* v_val_2282_, lean_object* v_a_x3f_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_st_ref_set(v_a_2281_, v_val_2282_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* v_a_2287_, lean_object* v_val_2288_, lean_object* v_a_x3f_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2287_, v_val_2288_, v_a_x3f_2289_);
lean_dec(v_a_x3f_2289_);
lean_dec(v_a_2287_);
return v_res_2291_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_unsigned_to_nat(16u);
v___x_2294_ = lean_mk_array(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
lean_ctor_set(v___x_2299_, 2, v___x_2298_);
lean_ctor_set(v___x_2299_, 3, v___x_2298_);
lean_ctor_set(v___x_2299_, 4, v___x_2298_);
lean_ctor_set(v___x_2299_, 5, v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t v_phase_2303_, lean_object* v_x_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_r_2310_; 
v___x_2308_ = lean_st_ref_get(v_a_2306_);
v___x_2309_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
v_r_2310_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_2304_, v___x_2309_, v_phase_2303_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v_r_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2327_; 
v_a_2311_ = lean_ctor_get(v_r_2310_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_r_2310_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2313_ = v_r_2310_;
v_isShared_2314_ = v_isSharedCheck_2327_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v_r_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2327_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
lean_inc(v_a_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set_tag(v___x_2313_, 1);
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
v___x_2317_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2306_, v___x_2308_, v___x_2316_);
lean_dec_ref(v___x_2316_);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v___x_2317_, 0);
lean_dec(v_unused_2325_);
v___x_2319_ = v___x_2317_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v___x_2317_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_a_2311_);
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2311_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_a_2328_ = lean_ctor_get(v_r_2310_, 0);
lean_inc(v_a_2328_);
lean_dec_ref(v_r_2310_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(v_a_2306_, v___x_2308_, v___x_2329_);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2330_, 0);
lean_dec(v_unused_2338_);
v___x_2332_ = v___x_2330_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v___x_2330_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 1);
lean_ctor_set(v___x_2332_, 0, v_a_2328_);
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2328_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* v_phase_2339_, lean_object* v_x_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
uint8_t v_phase_boxed_2344_; lean_object* v_res_2345_; 
v_phase_boxed_2344_ = lean_unbox(v_phase_2339_);
v_res_2345_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_boxed_2344_, v_x_2340_, v_a_2341_, v_a_2342_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* v_00_u03b1_2346_, uint8_t v_phase_2347_, lean_object* v_x_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2347_, v_x_2348_, v_a_2349_, v_a_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* v_00_u03b1_2353_, lean_object* v_phase_2354_, lean_object* v_x_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
uint8_t v_phase_boxed_2359_; lean_object* v_res_2360_; 
v_phase_boxed_2359_ = lean_unbox(v_phase_2354_);
v_res_2360_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(v_00_u03b1_2353_, v_phase_boxed_2359_, v_x_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t v_pu_2361_, lean_object* v_decl_2362_, lean_object* v___x_2363_, uint8_t v___x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Compiler_LCNF_Decl_internalize(v_pu_2361_, v_decl_2362_, v___x_2363_, v___x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = l_Lean_Compiler_LCNF_ppDecl(v_pu_2361_, v_a_2371_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
return v___x_2372_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2370_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2370_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* v_pu_2381_, lean_object* v_decl_2382_, lean_object* v___x_2383_, lean_object* v___x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_pu_boxed_2390_; uint8_t v___x_99__boxed_2391_; lean_object* v_res_2392_; 
v_pu_boxed_2390_ = lean_unbox(v_pu_2381_);
v___x_99__boxed_2391_ = lean_unbox(v___x_2384_);
v_res_2392_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(v_pu_boxed_2390_, v_decl_2382_, v___x_2383_, v___x_99__boxed_2391_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t v_pu_2393_, lean_object* v_decl_2394_, uint8_t v_phase_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; 
v___x_2399_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2400_ = 0;
v___x_2401_ = lean_box(v_pu_2393_);
v___x_2402_ = lean_box(v___x_2400_);
v___f_2403_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2403_, 0, v___x_2401_);
lean_closure_set(v___f_2403_, 1, v_decl_2394_);
lean_closure_set(v___f_2403_, 2, v___x_2399_);
lean_closure_set(v___f_2403_, 3, v___x_2402_);
v___x_2404_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2395_, v___f_2403_, v_a_2396_, v_a_2397_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* v_pu_2405_, lean_object* v_decl_2406_, lean_object* v_phase_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
uint8_t v_pu_boxed_2411_; uint8_t v_phase_boxed_2412_; lean_object* v_res_2413_; 
v_pu_boxed_2411_ = lean_unbox(v_pu_2405_);
v_phase_boxed_2412_ = lean_unbox(v_phase_2407_);
v_res_2413_ = l_Lean_Compiler_LCNF_ppDecl_x27(v_pu_boxed_2411_, v_decl_2406_, v_phase_boxed_2412_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t v_pu_2414_, lean_object* v_code_2415_, lean_object* v___x_2416_, uint8_t v___x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Compiler_LCNF_Code_internalize(v_pu_2414_, v_code_2415_, v___x_2416_, v___x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
v___x_2425_ = l_Lean_Compiler_LCNF_ppCode(v_pu_2414_, v_a_2424_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2423_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2423_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* v_pu_2434_, lean_object* v_code_2435_, lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
uint8_t v_pu_boxed_2443_; uint8_t v___x_99__boxed_2444_; lean_object* v_res_2445_; 
v_pu_boxed_2443_ = lean_unbox(v_pu_2434_);
v___x_99__boxed_2444_ = lean_unbox(v___x_2437_);
v_res_2445_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(v_pu_boxed_2443_, v_code_2435_, v___x_2436_, v___x_99__boxed_2444_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t v_pu_2446_, lean_object* v_code_2447_, uint8_t v_phase_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; 
v___x_2452_ = lean_obj_once(&l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1, &l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
v___x_2453_ = 0;
v___x_2454_ = lean_box(v_pu_2446_);
v___x_2455_ = lean_box(v___x_2453_);
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2456_, 0, v___x_2454_);
lean_closure_set(v___f_2456_, 1, v_code_2447_);
lean_closure_set(v___f_2456_, 2, v___x_2452_);
lean_closure_set(v___f_2456_, 3, v___x_2455_);
v___x_2457_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(v_phase_2448_, v___f_2456_, v_a_2449_, v_a_2450_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* v_pu_2458_, lean_object* v_code_2459_, lean_object* v_phase_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
uint8_t v_pu_boxed_2464_; uint8_t v_phase_boxed_2465_; lean_object* v_res_2466_; 
v_pu_boxed_2464_ = lean_unbox(v_pu_2458_);
v_phase_boxed_2465_ = lean_unbox(v_phase_2460_);
v_res_2466_ = l_Lean_Compiler_LCNF_ppCode_x27(v_pu_boxed_2464_, v_code_2459_, v_phase_boxed_2465_, v_a_2461_, v_a_2462_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2466_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

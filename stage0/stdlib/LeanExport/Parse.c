// Lean compiler output
// Module: LeanExport.Parse
// Imports: public import Std.Data.HashMap public import Lean.Declaration import Init.Data.Array.GetLit import Init.Data.String.Search import Init.System.IO import Std.Internal.Parsec.String import LeanExport.Json
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
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_LeanExport_Json_parse(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_instInhabitedExportedEnv_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_instInhabitedExportedEnv_default___closed__0;
static lean_once_cell_t l_LeanExport_instInhabitedExportedEnv_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_instInhabitedExportedEnv_default___closed__1;
static const lean_array_object l_LeanExport_instInhabitedExportedEnv_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LeanExport_instInhabitedExportedEnv_default___closed__2 = (const lean_object*)&l_LeanExport_instInhabitedExportedEnv_default___closed__2_value;
static lean_once_cell_t l_LeanExport_instInhabitedExportedEnv_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_instInhabitedExportedEnv_default___closed__3;
LEAN_EXPORT lean_object* l_LeanExport_instInhabitedExportedEnv_default;
LEAN_EXPORT lean_object* l_LeanExport_instInhabitedExportedEnv;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0;
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1;
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2;
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3;
static const lean_array_object l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Name not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Name index "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " bound twice"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Level not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Level index "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Expr not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Expr index "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "RecursorRule not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "RecursorRule index "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0_value;
static const lean_closure_object l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Duplicate declaration: "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid JSON: "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Expected JSON object"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Name.str invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2_value;
static lean_once_cell_t l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Name.num invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Level.succ invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Level.max invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Level.imax invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Level.param invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expr.bvar invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expr.sort invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Expr.const invalid"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "us"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Expr.app invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid binder info: "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Expr.lam invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Expr.forallE invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expr.letE invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nondep"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expr.proj invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeName"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "struct"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Expr.lit natVal invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Expr.lit strVal invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Expr.mdata invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to convert to name idx"};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__0_value)}};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "axiomInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "defnInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hints"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "safety"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "safe"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Unknown safety parameter: "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "thmInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "opaqueInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "quotInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unknown quot kind: "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inductInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "inductInfo invalid: Expected JSON object"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__8 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__8_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__8_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ctorInfo invalid"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "recInfo invalid"};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__0_value)}};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1_value;
static const lean_string_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2_value;
static const lean_string_object l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Inductive invalid, no `recs`"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Inductive invalid, no `ctors`"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__2_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Inductive invalid, no `types`"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__4_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "recs"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Unknown export object with keys "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "il"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ie"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23_value;
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_parseStream(lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_parseStream___boxed(lean_object*, lean_object*);
static lean_object* _init_l_LeanExport_instInhabitedExportedEnv_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_LeanExport_instInhabitedExportedEnv_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_LeanExport_instInhabitedExportedEnv_default___closed__0, &l_LeanExport_instInhabitedExportedEnv_default___closed__0_once, _init_l_LeanExport_instInhabitedExportedEnv_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_LeanExport_instInhabitedExportedEnv_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_LeanExport_instInhabitedExportedEnv_default___closed__2));
v___x_10_ = lean_obj_once(&l_LeanExport_instInhabitedExportedEnv_default___closed__1, &l_LeanExport_instInhabitedExportedEnv_default___closed__1_once, _init_l_LeanExport_instInhabitedExportedEnv_default___closed__1);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_LeanExport_instInhabitedExportedEnv_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_LeanExport_instInhabitedExportedEnv_default___closed__3, &l_LeanExport_instInhabitedExportedEnv_default___closed__3_once, _init_l_LeanExport_instInhabitedExportedEnv_default___closed__3);
return v___x_12_;
}
}
static lean_object* _init_l_LeanExport_instInhabitedExportedEnv(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_LeanExport_instInhabitedExportedEnv_default;
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
return v_x_14_;
}
else
{
lean_object* v_key_16_; lean_object* v_value_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_41_; 
v_key_16_ = lean_ctor_get(v_x_15_, 0);
v_value_17_ = lean_ctor_get(v_x_15_, 1);
v_tail_18_ = lean_ctor_get(v_x_15_, 2);
v_isSharedCheck_41_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_41_ == 0)
{
v___x_20_ = v_x_15_;
v_isShared_21_ = v_isSharedCheck_41_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_value_17_);
lean_inc(v_key_16_);
lean_dec(v_x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_41_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v_fold_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_22_ = lean_array_get_size(v_x_14_);
v___x_23_ = lean_uint64_of_nat(v_key_16_);
v___x_24_ = 32ULL;
v___x_25_ = lean_uint64_shift_right(v___x_23_, v___x_24_);
v_fold_26_ = lean_uint64_xor(v___x_23_, v___x_25_);
v___x_27_ = 16ULL;
v___x_28_ = lean_uint64_shift_right(v_fold_26_, v___x_27_);
v___x_29_ = lean_uint64_xor(v_fold_26_, v___x_28_);
v___x_30_ = lean_uint64_to_usize(v___x_29_);
v___x_31_ = lean_usize_of_nat(v___x_22_);
v___x_32_ = ((size_t)1ULL);
v___x_33_ = lean_usize_sub(v___x_31_, v___x_32_);
v___x_34_ = lean_usize_land(v___x_30_, v___x_33_);
v___x_35_ = lean_array_uget_borrowed(v_x_14_, v___x_34_);
lean_inc(v___x_35_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 2, v___x_35_);
v___x_37_ = v___x_20_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_key_16_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_value_17_);
lean_ctor_set(v_reuseFailAlloc_40_, 2, v___x_35_);
v___x_37_ = v_reuseFailAlloc_40_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
v___x_38_ = lean_array_uset(v_x_14_, v___x_34_, v___x_37_);
v_x_14_ = v___x_38_;
v_x_15_ = v_tail_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(lean_object* v_i_42_, lean_object* v_source_43_, lean_object* v_target_44_){
_start:
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_array_get_size(v_source_43_);
v___x_46_ = lean_nat_dec_lt(v_i_42_, v___x_45_);
if (v___x_46_ == 0)
{
lean_dec_ref(v_source_43_);
lean_dec(v_i_42_);
return v_target_44_;
}
else
{
lean_object* v_es_47_; lean_object* v___x_48_; lean_object* v_source_49_; lean_object* v_target_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_es_47_ = lean_array_fget(v_source_43_, v_i_42_);
v___x_48_ = lean_box(0);
v_source_49_ = lean_array_fset(v_source_43_, v_i_42_, v___x_48_);
v_target_50_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(v_target_44_, v_es_47_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_add(v_i_42_, v___x_51_);
lean_dec(v_i_42_);
v_i_42_ = v___x_52_;
v_source_43_ = v_source_49_;
v_target_44_ = v_target_50_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(lean_object* v_data_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_nbuckets_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_55_ = lean_array_get_size(v_data_54_);
v___x_56_ = lean_unsigned_to_nat(2u);
v_nbuckets_57_ = lean_nat_mul(v___x_55_, v___x_56_);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_box(0);
v___x_60_ = lean_mk_array(v_nbuckets_57_, v___x_59_);
v___x_61_ = lean_array_propagate_mark(v_data_54_, v___x_60_);
v___x_62_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(v___x_58_, v_data_54_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(lean_object* v_a_63_, lean_object* v_b_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_x_65_;
}
else
{
lean_object* v_key_66_; lean_object* v_value_67_; lean_object* v_tail_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_80_; 
v_key_66_ = lean_ctor_get(v_x_65_, 0);
v_value_67_ = lean_ctor_get(v_x_65_, 1);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_80_ == 0)
{
v___x_70_ = v_x_65_;
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_tail_68_);
lean_inc(v_value_67_);
lean_inc(v_key_66_);
lean_dec(v_x_65_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_eq(v_key_66_, v_a_63_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_63_, v_b_64_, v_tail_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 2, v___x_73_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_key_66_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_value_67_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v_value_67_);
lean_dec(v_key_66_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v_b_64_);
lean_ctor_set(v___x_70_, 0, v_a_63_);
v___x_78_ = v___x_70_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_b_64_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_tail_68_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(lean_object* v_a_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
else
{
lean_object* v_key_84_; lean_object* v_tail_85_; uint8_t v___x_86_; 
v_key_84_ = lean_ctor_get(v_x_82_, 0);
v_tail_85_ = lean_ctor_get(v_x_82_, 2);
v___x_86_ = lean_nat_dec_eq(v_key_84_, v_a_81_);
if (v___x_86_ == 0)
{
v_x_82_ = v_tail_85_;
goto _start;
}
else
{
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_88_, v_x_89_);
lean_dec(v_x_89_);
lean_dec(v_a_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(lean_object* v_m_92_, lean_object* v_a_93_, lean_object* v_b_94_){
_start:
{
lean_object* v_size_95_; lean_object* v_buckets_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_139_; 
v_size_95_ = lean_ctor_get(v_m_92_, 0);
v_buckets_96_ = lean_ctor_get(v_m_92_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_m_92_);
if (v_isSharedCheck_139_ == 0)
{
v___x_98_ = v_m_92_;
v_isShared_99_ = v_isSharedCheck_139_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_buckets_96_);
lean_inc(v_size_95_);
lean_dec(v_m_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_139_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v_fold_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v_bkt_113_; uint8_t v___x_114_; 
v___x_100_ = lean_array_get_size(v_buckets_96_);
v___x_101_ = lean_uint64_of_nat(v_a_93_);
v___x_102_ = 32ULL;
v___x_103_ = lean_uint64_shift_right(v___x_101_, v___x_102_);
v_fold_104_ = lean_uint64_xor(v___x_101_, v___x_103_);
v___x_105_ = 16ULL;
v___x_106_ = lean_uint64_shift_right(v_fold_104_, v___x_105_);
v___x_107_ = lean_uint64_xor(v_fold_104_, v___x_106_);
v___x_108_ = lean_uint64_to_usize(v___x_107_);
v___x_109_ = lean_usize_of_nat(v___x_100_);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_sub(v___x_109_, v___x_110_);
v___x_112_ = lean_usize_land(v___x_108_, v___x_111_);
v_bkt_113_ = lean_array_uget_borrowed(v_buckets_96_, v___x_112_);
v___x_114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_93_, v_bkt_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v_size_x27_116_; lean_object* v___x_117_; lean_object* v_buckets_x27_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v_size_x27_116_ = lean_nat_add(v_size_95_, v___x_115_);
lean_dec(v_size_95_);
lean_inc(v_bkt_113_);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v_a_93_);
lean_ctor_set(v___x_117_, 1, v_b_94_);
lean_ctor_set(v___x_117_, 2, v_bkt_113_);
v_buckets_x27_118_ = lean_array_uset(v_buckets_96_, v___x_112_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(4u);
v___x_120_ = lean_nat_mul(v_size_x27_116_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = lean_nat_div(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_array_get_size(v_buckets_x27_118_);
v___x_124_ = lean_nat_dec_le(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
if (v___x_124_ == 0)
{
lean_object* v_val_125_; lean_object* v___x_127_; 
v_val_125_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_buckets_x27_118_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_val_125_);
lean_ctor_set(v___x_98_, 0, v_size_x27_116_);
v___x_127_ = v___x_98_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_size_x27_116_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_val_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v___x_130_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_buckets_x27_118_);
lean_ctor_set(v___x_98_, 0, v_size_x27_116_);
v___x_130_ = v___x_98_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_size_x27_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_buckets_x27_118_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v___x_132_; lean_object* v_buckets_x27_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
lean_inc(v_bkt_113_);
v___x_132_ = lean_box(0);
v_buckets_x27_133_ = lean_array_uset(v_buckets_96_, v___x_112_, v___x_132_);
v___x_134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_93_, v_b_94_, v_bkt_113_);
v___x_135_ = lean_array_uset(v_buckets_x27_133_, v___x_112_, v___x_134_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_135_);
v___x_137_ = v___x_98_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_size_95_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_unsigned_to_nat(16u);
v___x_142_ = lean_mk_array(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_149_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_148_, v___x_147_, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_152_, v___x_151_, v___x_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(lean_object* v_x_156_, lean_object* v_stream_157_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_159_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_160_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2);
v___x_161_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3);
v___x_162_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4));
v___x_163_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_163_, 0, v_stream_157_);
lean_ctor_set(v___x_163_, 1, v___x_160_);
lean_ctor_set(v___x_163_, 2, v___x_161_);
lean_ctor_set(v___x_163_, 3, v___x_159_);
lean_ctor_set(v___x_163_, 4, v___x_159_);
lean_ctor_set(v___x_163_, 5, v___x_159_);
lean_ctor_set(v___x_163_, 6, v___x_162_);
v___x_164_ = lean_apply_2(v_x_156_, v___x_163_, lean_box(0));
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___boxed(lean_object* v_x_165_, lean_object* v_stream_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_165_, v_stream_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(lean_object* v_00_u03b1_169_, lean_object* v_x_170_, lean_object* v_stream_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_170_, v_stream_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___boxed(lean_object* v_00_u03b1_174_, lean_object* v_x_175_, lean_object* v_stream_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(v_00_u03b1_174_, v_x_175_, v_stream_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_m_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_m_180_, v_a_181_, v_b_182_);
return v___x_183_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_185_, v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_188_, lean_object* v_a_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(v_00_u03b2_188_, v_a_189_, v_x_190_);
lean_dec(v_x_190_);
lean_dec(v_a_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1(lean_object* v_00_u03b2_193_, lean_object* v_data_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_data_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2(lean_object* v_00_u03b2_196_, lean_object* v_a_197_, lean_object* v_b_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_197_, v_b_198_, v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_201_, lean_object* v_i_202_, lean_object* v_source_203_, lean_object* v_target_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(v_i_202_, v_source_203_, v_target_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(v_x_207_, v_x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(lean_object* v_msg_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_212_, 0, v_msg_210_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg___boxed(lean_object* v_msg_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(v_msg_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail(lean_object* v_00_u03b1_217_, lean_object* v_msg_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_221_, 0, v_msg_218_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___boxed(lean_object* v_00_u03b1_223_, lean_object* v_msg_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail(v_00_u03b1_223_, v_msg_224_, v_a_225_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1(void){
_start:
{
lean_object* v___x_229_; lean_object* v___f_230_; 
v___x_229_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_230_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_230_, 0, v___x_229_);
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName(lean_object* v_nidx_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_nameMap_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___x_238_; 
v_nameMap_235_ = lean_ctor_get(v_a_233_, 1);
v___f_236_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_237_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_nidx_232_);
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_237_, v___f_236_, v_nameMap_235_, v_nidx_232_);
if (lean_obj_tag(v___x_238_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_nidx_232_);
v_val_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_val_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_val_239_);
lean_ctor_set(v___x_243_, 1, v_a_233_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 0);
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___x_238_);
lean_dec_ref(v_a_233_);
v___x_248_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_249_ = l_Nat_reprFast(v_nidx_232_);
v___x_250_ = lean_string_append(v___x_248_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___boxed(lean_object* v_nidx_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getName(v_nidx_253_, v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object* v_nidx_259_, lean_object* v_n_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_stream_263_; lean_object* v_nameMap_264_; lean_object* v_levelMap_265_; lean_object* v_exprMap_266_; lean_object* v_recursorRuleMap_267_; lean_object* v_constMap_268_; lean_object* v_constOrder_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_290_; 
v_stream_263_ = lean_ctor_get(v_a_261_, 0);
v_nameMap_264_ = lean_ctor_get(v_a_261_, 1);
v_levelMap_265_ = lean_ctor_get(v_a_261_, 2);
v_exprMap_266_ = lean_ctor_get(v_a_261_, 3);
v_recursorRuleMap_267_ = lean_ctor_get(v_a_261_, 4);
v_constMap_268_ = lean_ctor_get(v_a_261_, 5);
v_constOrder_269_ = lean_ctor_get(v_a_261_, 6);
v_isSharedCheck_290_ = !lean_is_exclusive(v_a_261_);
if (v_isSharedCheck_290_ == 0)
{
v___x_271_ = v_a_261_;
v_isShared_272_ = v_isSharedCheck_290_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_constOrder_269_);
lean_inc(v_constMap_268_);
lean_inc(v_recursorRuleMap_267_);
lean_inc(v_exprMap_266_);
lean_inc(v_levelMap_265_);
lean_inc(v_nameMap_264_);
lean_inc(v_stream_263_);
lean_dec(v_a_261_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_290_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___f_273_; lean_object* v___f_274_; uint8_t v___x_275_; 
v___f_273_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_274_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_nidx_259_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_274_, v___f_273_, v_nameMap_264_, v_nidx_259_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_274_, v___f_273_, v_nameMap_264_, v_nidx_259_, v_n_260_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_277_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_stream_263_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_levelMap_265_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_exprMap_266_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_recursorRuleMap_267_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v_constMap_268_);
lean_ctor_set(v_reuseFailAlloc_282_, 6, v_constOrder_269_);
v___x_279_ = v_reuseFailAlloc_282_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_276_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_del_object(v___x_271_);
lean_dec_ref(v_constOrder_269_);
lean_dec_ref(v_constMap_268_);
lean_dec_ref(v_recursorRuleMap_267_);
lean_dec_ref(v_exprMap_266_);
lean_dec_ref(v_levelMap_265_);
lean_dec_ref(v_nameMap_264_);
lean_dec_ref(v_stream_263_);
lean_dec(v_n_260_);
v___x_283_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_284_ = l_Nat_reprFast(v_nidx_259_);
v___x_285_ = lean_string_append(v___x_283_, v___x_284_);
lean_dec_ref(v___x_284_);
v___x_286_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
v___x_288_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object* v_nidx_291_, lean_object* v_n_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addName(v_nidx_291_, v_n_292_, v_a_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object* v_uidx_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_levelMap_300_; lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___x_303_; 
v_levelMap_300_ = lean_ctor_get(v_a_298_, 2);
v___f_301_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_302_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_297_);
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_302_, v___f_301_, v_levelMap_300_, v_uidx_297_);
if (lean_obj_tag(v___x_303_) == 1)
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_uidx_297_);
v_val_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_val_304_);
lean_ctor_set(v___x_308_, 1, v_a_298_);
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 0);
lean_ctor_set(v___x_306_, 0, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___x_303_);
lean_dec_ref(v_a_298_);
v___x_313_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_314_ = l_Nat_reprFast(v_uidx_297_);
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
lean_dec_ref(v___x_314_);
v___x_316_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object* v_uidx_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(v_uidx_318_, v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object* v_uidx_323_, lean_object* v_l_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_stream_327_; lean_object* v_nameMap_328_; lean_object* v_levelMap_329_; lean_object* v_exprMap_330_; lean_object* v_recursorRuleMap_331_; lean_object* v_constMap_332_; lean_object* v_constOrder_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_354_; 
v_stream_327_ = lean_ctor_get(v_a_325_, 0);
v_nameMap_328_ = lean_ctor_get(v_a_325_, 1);
v_levelMap_329_ = lean_ctor_get(v_a_325_, 2);
v_exprMap_330_ = lean_ctor_get(v_a_325_, 3);
v_recursorRuleMap_331_ = lean_ctor_get(v_a_325_, 4);
v_constMap_332_ = lean_ctor_get(v_a_325_, 5);
v_constOrder_333_ = lean_ctor_get(v_a_325_, 6);
v_isSharedCheck_354_ = !lean_is_exclusive(v_a_325_);
if (v_isSharedCheck_354_ == 0)
{
v___x_335_ = v_a_325_;
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_constOrder_333_);
lean_inc(v_constMap_332_);
lean_inc(v_recursorRuleMap_331_);
lean_inc(v_exprMap_330_);
lean_inc(v_levelMap_329_);
lean_inc(v_nameMap_328_);
lean_inc(v_stream_327_);
lean_dec(v_a_325_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___f_337_; lean_object* v___f_338_; uint8_t v___x_339_; 
v___f_337_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_338_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_323_);
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_338_, v___f_337_, v_levelMap_329_, v_uidx_323_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = lean_box(0);
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_338_, v___f_337_, v_levelMap_329_, v_uidx_323_, v_l_324_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 2, v___x_341_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_stream_327_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_nameMap_328_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_exprMap_330_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_recursorRuleMap_331_);
lean_ctor_set(v_reuseFailAlloc_346_, 5, v_constMap_332_);
lean_ctor_set(v_reuseFailAlloc_346_, 6, v_constOrder_333_);
v___x_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_del_object(v___x_335_);
lean_dec_ref(v_constOrder_333_);
lean_dec_ref(v_constMap_332_);
lean_dec_ref(v_recursorRuleMap_331_);
lean_dec_ref(v_exprMap_330_);
lean_dec_ref(v_levelMap_329_);
lean_dec_ref(v_nameMap_328_);
lean_dec_ref(v_stream_327_);
lean_dec(v_l_324_);
v___x_347_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_348_ = l_Nat_reprFast(v_uidx_323_);
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
lean_dec_ref(v___x_348_);
v___x_350_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
v___x_352_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object* v_uidx_355_, lean_object* v_l_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(v_uidx_355_, v_l_356_, v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object* v_eidx_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_exprMap_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___x_367_; 
v_exprMap_364_ = lean_ctor_get(v_a_362_, 3);
v___f_365_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_366_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_361_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_366_, v___f_365_, v_exprMap_364_, v_eidx_361_);
if (lean_obj_tag(v___x_367_) == 1)
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_eidx_361_);
v_val_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_val_368_);
lean_ctor_set(v___x_372_, 1, v_a_362_);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 0);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v___x_367_);
lean_dec_ref(v_a_362_);
v___x_377_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_378_ = l_Nat_reprFast(v_eidx_361_);
v___x_379_ = lean_string_append(v___x_377_, v___x_378_);
lean_dec_ref(v___x_378_);
v___x_380_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object* v_eidx_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(v_eidx_382_, v_a_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object* v_eidx_387_, lean_object* v_e_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_stream_391_; lean_object* v_nameMap_392_; lean_object* v_levelMap_393_; lean_object* v_exprMap_394_; lean_object* v_recursorRuleMap_395_; lean_object* v_constMap_396_; lean_object* v_constOrder_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_418_; 
v_stream_391_ = lean_ctor_get(v_a_389_, 0);
v_nameMap_392_ = lean_ctor_get(v_a_389_, 1);
v_levelMap_393_ = lean_ctor_get(v_a_389_, 2);
v_exprMap_394_ = lean_ctor_get(v_a_389_, 3);
v_recursorRuleMap_395_ = lean_ctor_get(v_a_389_, 4);
v_constMap_396_ = lean_ctor_get(v_a_389_, 5);
v_constOrder_397_ = lean_ctor_get(v_a_389_, 6);
v_isSharedCheck_418_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_418_ == 0)
{
v___x_399_ = v_a_389_;
v_isShared_400_ = v_isSharedCheck_418_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_constOrder_397_);
lean_inc(v_constMap_396_);
lean_inc(v_recursorRuleMap_395_);
lean_inc(v_exprMap_394_);
lean_inc(v_levelMap_393_);
lean_inc(v_nameMap_392_);
lean_inc(v_stream_391_);
lean_dec(v_a_389_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_418_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___f_401_; lean_object* v___f_402_; uint8_t v___x_403_; 
v___f_401_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_402_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_387_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_402_, v___f_401_, v_exprMap_394_, v_eidx_387_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = lean_box(0);
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_402_, v___f_401_, v_exprMap_394_, v_eidx_387_, v_e_388_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 3, v___x_405_);
v___x_407_ = v___x_399_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_stream_391_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_nameMap_392_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_levelMap_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_recursorRuleMap_395_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_constMap_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_constOrder_397_);
v___x_407_ = v_reuseFailAlloc_410_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_del_object(v___x_399_);
lean_dec_ref(v_constOrder_397_);
lean_dec_ref(v_constMap_396_);
lean_dec_ref(v_recursorRuleMap_395_);
lean_dec_ref(v_exprMap_394_);
lean_dec_ref(v_levelMap_393_);
lean_dec_ref(v_nameMap_392_);
lean_dec_ref(v_stream_391_);
lean_dec_ref(v_e_388_);
v___x_411_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_412_ = l_Nat_reprFast(v_eidx_387_);
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
lean_dec_ref(v___x_412_);
v___x_414_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
v___x_416_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object* v_eidx_419_, lean_object* v_e_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(v_eidx_419_, v_e_420_, v_a_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object* v_ridx_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_recursorRuleMap_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___x_431_; 
v_recursorRuleMap_428_ = lean_ctor_get(v_a_426_, 4);
v___f_429_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_430_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_425_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_430_, v___f_429_, v_recursorRuleMap_428_, v_ridx_425_);
if (lean_obj_tag(v___x_431_) == 1)
{
lean_object* v_val_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_ridx_425_);
v_val_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_val_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_val_432_);
lean_ctor_set(v___x_436_, 1, v_a_426_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v___x_431_);
lean_dec_ref(v_a_426_);
v___x_441_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0));
v___x_442_ = l_Nat_reprFast(v_ridx_425_);
v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object* v_ridx_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(v_ridx_446_, v_a_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(lean_object* v_ridx_451_, lean_object* v_r_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_stream_455_; lean_object* v_nameMap_456_; lean_object* v_levelMap_457_; lean_object* v_exprMap_458_; lean_object* v_recursorRuleMap_459_; lean_object* v_constMap_460_; lean_object* v_constOrder_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_482_; 
v_stream_455_ = lean_ctor_get(v_a_453_, 0);
v_nameMap_456_ = lean_ctor_get(v_a_453_, 1);
v_levelMap_457_ = lean_ctor_get(v_a_453_, 2);
v_exprMap_458_ = lean_ctor_get(v_a_453_, 3);
v_recursorRuleMap_459_ = lean_ctor_get(v_a_453_, 4);
v_constMap_460_ = lean_ctor_get(v_a_453_, 5);
v_constOrder_461_ = lean_ctor_get(v_a_453_, 6);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_482_ == 0)
{
v___x_463_ = v_a_453_;
v_isShared_464_ = v_isSharedCheck_482_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_constOrder_461_);
lean_inc(v_constMap_460_);
lean_inc(v_recursorRuleMap_459_);
lean_inc(v_exprMap_458_);
lean_inc(v_levelMap_457_);
lean_inc(v_nameMap_456_);
lean_inc(v_stream_455_);
lean_dec(v_a_453_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_482_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___f_465_; lean_object* v___f_466_; uint8_t v___x_467_; 
v___f_465_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_466_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_451_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_466_, v___f_465_, v_recursorRuleMap_459_, v_ridx_451_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_box(0);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_466_, v___f_465_, v_recursorRuleMap_459_, v_ridx_451_, v_r_452_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 4, v___x_469_);
v___x_471_ = v___x_463_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_stream_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_nameMap_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_levelMap_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_exprMap_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_constMap_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_constOrder_461_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_468_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_del_object(v___x_463_);
lean_dec_ref(v_constOrder_461_);
lean_dec_ref(v_constMap_460_);
lean_dec_ref(v_recursorRuleMap_459_);
lean_dec_ref(v_exprMap_458_);
lean_dec_ref(v_levelMap_457_);
lean_dec_ref(v_nameMap_456_);
lean_dec_ref(v_stream_455_);
lean_dec_ref(v_r_452_);
v___x_475_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___closed__0));
v___x_476_ = l_Nat_reprFast(v_ridx_451_);
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___boxed(lean_object* v_ridx_483_, lean_object* v_r_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(v_ridx_483_, v_r_484_, v_a_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(lean_object* v_name_491_, lean_object* v_d_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_stream_495_; lean_object* v_nameMap_496_; lean_object* v_levelMap_497_; lean_object* v_exprMap_498_; lean_object* v_recursorRuleMap_499_; lean_object* v_constMap_500_; lean_object* v_constOrder_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_521_; 
v_stream_495_ = lean_ctor_get(v_a_493_, 0);
v_nameMap_496_ = lean_ctor_get(v_a_493_, 1);
v_levelMap_497_ = lean_ctor_get(v_a_493_, 2);
v_exprMap_498_ = lean_ctor_get(v_a_493_, 3);
v_recursorRuleMap_499_ = lean_ctor_get(v_a_493_, 4);
v_constMap_500_ = lean_ctor_get(v_a_493_, 5);
v_constOrder_501_ = lean_ctor_get(v_a_493_, 6);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_521_ == 0)
{
v___x_503_ = v_a_493_;
v_isShared_504_ = v_isSharedCheck_521_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_constOrder_501_);
lean_inc(v_constMap_500_);
lean_inc(v_recursorRuleMap_499_);
lean_inc(v_exprMap_498_);
lean_inc(v_levelMap_497_);
lean_inc(v_nameMap_496_);
lean_inc(v_stream_495_);
lean_dec(v_a_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_521_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0));
v___x_506_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1));
lean_inc(v_name_491_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_505_, v___x_506_, v_constMap_500_, v_name_491_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_508_ = lean_box(0);
lean_inc(v_name_491_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_505_, v___x_506_, v_constMap_500_, v_name_491_, v_d_492_);
v___x_510_ = lean_array_push(v_constOrder_501_, v_name_491_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 6, v___x_510_);
lean_ctor_set(v___x_503_, 5, v___x_509_);
v___x_512_ = v___x_503_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_stream_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_nameMap_496_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_levelMap_497_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_exprMap_498_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_recursorRuleMap_499_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v___x_510_);
v___x_512_ = v_reuseFailAlloc_515_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_508_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_503_);
lean_dec_ref(v_constOrder_501_);
lean_dec_ref(v_constMap_500_);
lean_dec_ref(v_recursorRuleMap_499_);
lean_dec_ref(v_exprMap_498_);
lean_dec_ref(v_levelMap_497_);
lean_dec_ref(v_nameMap_496_);
lean_dec_ref(v_stream_495_);
lean_dec_ref(v_d_492_);
v___x_516_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_491_, v___x_507_);
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___boxed(lean_object* v_name_522_, lean_object* v_d_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(v_name_522_, v_d_523_, v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(lean_object* v_line_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_LeanExport_Json_parse(v_line_531_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_a_532_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_545_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0));
v___x_540_ = lean_string_append(v___x_539_, v_a_535_);
lean_dec(v_a_535_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 18);
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_544_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_563_; 
v_a_546_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_563_ == 0)
{
v___x_548_ = v___x_534_;
v_isShared_549_ = v_isSharedCheck_563_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_534_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_563_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
if (lean_obj_tag(v_a_546_) == 5)
{
lean_object* v_kvPairs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
lean_del_object(v___x_548_);
v_kvPairs_550_ = lean_ctor_get(v_a_546_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_a_546_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_kvPairs_550_);
lean_dec(v_a_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v_kvPairs_550_);
lean_ctor_set(v___x_554_, 1, v_a_532_);
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 0);
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec(v_a_546_);
lean_dec_ref(v_a_532_);
v___x_559_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_559_);
v___x_561_ = v___x_548_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___boxed(lean_object* v_line_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(v_line_564_, v_a_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
lean_object* v_key_571_; lean_object* v_value_572_; lean_object* v_tail_573_; uint8_t v___x_574_; 
v_key_571_ = lean_ctor_get(v_x_569_, 0);
v_value_572_ = lean_ctor_get(v_x_569_, 1);
v_tail_573_ = lean_ctor_get(v_x_569_, 2);
v___x_574_ = lean_nat_dec_eq(v_key_571_, v_a_568_);
if (v___x_574_ == 0)
{
v_x_569_ = v_tail_573_;
goto _start;
}
else
{
lean_object* v___x_576_; 
lean_inc(v_value_572_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_value_572_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg___boxed(lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_577_, v_x_578_);
lean_dec(v_x_578_);
lean_dec(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(lean_object* v_m_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_buckets_582_; lean_object* v___x_583_; uint64_t v___x_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v_fold_587_; uint64_t v___x_588_; uint64_t v___x_589_; uint64_t v___x_590_; size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_buckets_582_ = lean_ctor_get(v_m_580_, 1);
v___x_583_ = lean_array_get_size(v_buckets_582_);
v___x_584_ = lean_uint64_of_nat(v_a_581_);
v___x_585_ = 32ULL;
v___x_586_ = lean_uint64_shift_right(v___x_584_, v___x_585_);
v_fold_587_ = lean_uint64_xor(v___x_584_, v___x_586_);
v___x_588_ = 16ULL;
v___x_589_ = lean_uint64_shift_right(v_fold_587_, v___x_588_);
v___x_590_ = lean_uint64_xor(v_fold_587_, v___x_589_);
v___x_591_ = lean_uint64_to_usize(v___x_590_);
v___x_592_ = lean_usize_of_nat(v___x_583_);
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_sub(v___x_592_, v___x_593_);
v___x_595_ = lean_usize_land(v___x_591_, v___x_594_);
v___x_596_ = lean_array_uget_borrowed(v_buckets_582_, v___x_595_);
v___x_597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_581_, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg___boxed(lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_m_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(lean_object* v_t_601_, lean_object* v_k_602_){
_start:
{
if (lean_obj_tag(v_t_601_) == 0)
{
lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v_l_605_; lean_object* v_r_606_; uint8_t v___x_607_; 
v_k_603_ = lean_ctor_get(v_t_601_, 1);
v_v_604_ = lean_ctor_get(v_t_601_, 2);
v_l_605_ = lean_ctor_get(v_t_601_, 3);
v_r_606_ = lean_ctor_get(v_t_601_, 4);
v___x_607_ = lean_string_compare(v_k_602_, v_k_603_);
switch(v___x_607_)
{
case 0:
{
v_t_601_ = v_l_605_;
goto _start;
}
case 1:
{
lean_object* v___x_609_; 
lean_inc(v_v_604_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_v_604_);
return v___x_609_;
}
default: 
{
v_t_601_ = v_r_606_;
goto _start;
}
}
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg___boxed(lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_612_, v_k_613_);
lean_dec_ref(v_k_613_);
lean_dec(v_t_612_);
return v_res_614_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3(void){
_start:
{
lean_object* v_natZero_619_; lean_object* v_intZero_620_; 
v_natZero_619_ = lean_unsigned_to_nat(0u);
v_intZero_620_ = lean_nat_to_int(v_natZero_619_);
return v_intZero_620_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(lean_object* v_json_622_, lean_object* v_a_623_){
_start:
{
if (lean_obj_tag(v_json_622_) == 5)
{
lean_object* v_kvPairs_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_kvPairs_631_ = lean_ctor_get(v_json_622_, 0);
v___x_632_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_631_, v___x_632_);
if (lean_obj_tag(v___x_633_) == 1)
{
lean_object* v_val_634_; 
v_val_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v___x_633_, 1);
if (lean_obj_tag(v_val_634_) == 2)
{
lean_object* v_n_635_; lean_object* v_mantissa_636_; lean_object* v_exponent_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_681_; 
v_n_635_ = lean_ctor_get(v_val_634_, 0);
lean_inc_ref(v_n_635_);
lean_dec_ref_known(v_val_634_, 1);
v_mantissa_636_ = lean_ctor_get(v_n_635_, 0);
v_exponent_637_ = lean_ctor_get(v_n_635_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_n_635_);
if (v_isSharedCheck_681_ == 0)
{
v___x_639_ = v_n_635_;
v_isShared_640_ = v_isSharedCheck_681_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_exponent_637_);
lean_inc(v_mantissa_636_);
lean_dec(v_n_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_681_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_natZero_641_; lean_object* v_intZero_642_; uint8_t v_isNeg_643_; 
v_natZero_641_ = lean_unsigned_to_nat(0u);
v_intZero_642_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_643_ = lean_int_dec_lt(v_mantissa_636_, v_intZero_642_);
if (v_isNeg_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_eq(v_exponent_637_, v_natZero_641_);
lean_dec(v_exponent_637_);
if (v___x_644_ == 0)
{
lean_del_object(v___x_639_);
lean_dec(v_mantissa_636_);
lean_dec_ref(v_a_623_);
goto v___jp_625_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_646_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_631_, v___x_645_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_680_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_680_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_680_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_val_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_680_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
if (lean_obj_tag(v_val_647_) == 3)
{
lean_object* v_s_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_679_; 
v_s_651_ = lean_ctor_get(v_val_647_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_val_647_);
if (v_isSharedCheck_679_ == 0)
{
v___x_653_ = v_val_647_;
v_isShared_654_ = v_isSharedCheck_679_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_s_651_);
lean_dec(v_val_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_679_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_nameMap_655_; lean_object* v_a_656_; lean_object* v___x_657_; 
v_nameMap_655_ = lean_ctor_get(v_a_623_, 1);
v_a_656_ = lean_nat_abs(v_mantissa_636_);
lean_dec(v_mantissa_636_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_655_, v_a_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_656_);
lean_del_object(v___x_653_);
lean_del_object(v___x_649_);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_669_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = l_Lean_Name_str___override(v_val_658_, v_s_651_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_a_623_);
lean_ctor_set(v___x_639_, 0, v___x_662_);
v___x_664_ = v___x_639_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_623_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 0);
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
lean_dec(v___x_657_);
lean_dec_ref(v_s_651_);
lean_del_object(v___x_639_);
lean_dec_ref(v_a_623_);
v___x_670_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_671_ = l_Nat_reprFast(v_a_656_);
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
lean_dec_ref(v___x_671_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 18);
lean_ctor_set(v___x_653_, 0, v___x_672_);
v___x_674_ = v___x_653_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_674_);
v___x_676_ = v___x_649_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_del_object(v___x_649_);
lean_dec(v_val_647_);
lean_del_object(v___x_639_);
lean_dec(v_mantissa_636_);
lean_dec_ref(v_a_623_);
goto v___jp_628_;
}
}
}
else
{
lean_dec(v___x_646_);
lean_del_object(v___x_639_);
lean_dec(v_mantissa_636_);
lean_dec_ref(v_a_623_);
goto v___jp_628_;
}
}
}
else
{
lean_del_object(v___x_639_);
lean_dec(v_exponent_637_);
lean_dec(v_mantissa_636_);
lean_dec_ref(v_a_623_);
goto v___jp_625_;
}
}
}
else
{
lean_dec(v_val_634_);
lean_dec_ref(v_a_623_);
goto v___jp_625_;
}
}
else
{
lean_dec(v___x_633_);
lean_dec_ref(v_a_623_);
goto v___jp_625_;
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v_a_623_);
v___x_682_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
v___jp_625_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
v___jp_628_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___boxed(lean_object* v_json_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_json_684_, v_a_685_);
lean_dec(v_json_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(lean_object* v_00_u03b4_688_, lean_object* v_t_689_, lean_object* v_k_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_689_, v_k_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___boxed(lean_object* v_00_u03b4_692_, lean_object* v_t_693_, lean_object* v_k_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(v_00_u03b4_692_, v_t_693_, v_k_694_);
lean_dec_ref(v_k_694_);
lean_dec(v_t_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(lean_object* v_00_u03b2_696_, lean_object* v_m_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_697_, v_a_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___boxed(lean_object* v_00_u03b2_700_, lean_object* v_m_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(v_00_u03b2_700_, v_m_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_m_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(lean_object* v_00_u03b2_704_, lean_object* v_a_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___boxed(lean_object* v_00_u03b2_708_, lean_object* v_a_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(v_00_u03b2_708_, v_a_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec(v_a_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(lean_object* v_json_716_, lean_object* v_a_717_){
_start:
{
if (lean_obj_tag(v_json_716_) == 5)
{
lean_object* v_kvPairs_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_kvPairs_725_ = lean_ctor_get(v_json_716_, 0);
v___x_726_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_727_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_725_, v___x_726_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_727_, 1);
if (lean_obj_tag(v_val_728_) == 2)
{
lean_object* v_n_729_; lean_object* v_mantissa_730_; lean_object* v_exponent_731_; lean_object* v_natZero_732_; lean_object* v_intZero_733_; uint8_t v_isNeg_734_; 
v_n_729_ = lean_ctor_get(v_val_728_, 0);
lean_inc_ref(v_n_729_);
lean_dec_ref_known(v_val_728_, 1);
v_mantissa_730_ = lean_ctor_get(v_n_729_, 0);
lean_inc(v_mantissa_730_);
v_exponent_731_ = lean_ctor_get(v_n_729_, 1);
lean_inc(v_exponent_731_);
lean_dec_ref(v_n_729_);
v_natZero_732_ = lean_unsigned_to_nat(0u);
v_intZero_733_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_734_ = lean_int_dec_lt(v_mantissa_730_, v_intZero_733_);
if (v_isNeg_734_ == 0)
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_eq(v_exponent_731_, v_natZero_732_);
lean_dec(v_exponent_731_);
if (v___x_735_ == 0)
{
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_719_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2));
v___x_737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_725_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 1)
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_780_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_780_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_780_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_780_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_val_738_) == 2)
{
lean_object* v_n_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_779_; 
v_n_742_ = lean_ctor_get(v_val_738_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_val_738_);
if (v_isSharedCheck_779_ == 0)
{
v___x_744_ = v_val_738_;
v_isShared_745_ = v_isSharedCheck_779_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_n_742_);
lean_dec(v_val_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_779_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_mantissa_746_; lean_object* v_exponent_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_778_; 
v_mantissa_746_ = lean_ctor_get(v_n_742_, 0);
v_exponent_747_ = lean_ctor_get(v_n_742_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_n_742_);
if (v_isSharedCheck_778_ == 0)
{
v___x_749_ = v_n_742_;
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_exponent_747_);
lean_inc(v_mantissa_746_);
lean_dec(v_n_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
uint8_t v_isNeg_751_; 
v_isNeg_751_ = lean_int_dec_lt(v_mantissa_746_, v_intZero_733_);
if (v_isNeg_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_eq(v_exponent_747_, v_natZero_732_);
lean_dec(v_exponent_747_);
if (v___x_752_ == 0)
{
lean_del_object(v___x_749_);
lean_dec(v_mantissa_746_);
lean_del_object(v___x_744_);
lean_del_object(v___x_740_);
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_722_;
}
else
{
lean_object* v_nameMap_753_; lean_object* v_a_754_; lean_object* v___x_755_; 
v_nameMap_753_ = lean_ctor_get(v_a_717_, 1);
v_a_754_ = lean_nat_abs(v_mantissa_730_);
lean_dec(v_mantissa_730_);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_753_, v_a_754_);
if (lean_obj_tag(v___x_755_) == 1)
{
lean_object* v_val_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_754_);
lean_del_object(v___x_744_);
lean_del_object(v___x_740_);
v_val_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_768_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_val_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v_a_760_ = lean_nat_abs(v_mantissa_746_);
lean_dec(v_mantissa_746_);
v___x_761_ = l_Lean_Name_num___override(v_val_756_, v_a_760_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_a_717_);
lean_ctor_set(v___x_749_, 0, v___x_761_);
v___x_763_ = v___x_749_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_717_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set_tag(v___x_758_, 0);
lean_ctor_set(v___x_758_, 0, v___x_763_);
v___x_765_ = v___x_758_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v___x_755_);
lean_del_object(v___x_749_);
lean_dec(v_mantissa_746_);
lean_dec_ref(v_a_717_);
v___x_769_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_770_ = l_Nat_reprFast(v_a_754_);
v___x_771_ = lean_string_append(v___x_769_, v___x_770_);
lean_dec_ref(v___x_770_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 18);
lean_ctor_set(v___x_744_, 0, v___x_771_);
v___x_773_ = v___x_744_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_773_);
v___x_775_ = v___x_740_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_del_object(v___x_749_);
lean_dec(v_exponent_747_);
lean_dec(v_mantissa_746_);
lean_del_object(v___x_744_);
lean_del_object(v___x_740_);
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_722_;
}
}
}
}
else
{
lean_del_object(v___x_740_);
lean_dec(v_val_738_);
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_722_;
}
}
}
else
{
lean_dec(v___x_737_);
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_722_;
}
}
}
else
{
lean_dec(v_exponent_731_);
lean_dec(v_mantissa_730_);
lean_dec_ref(v_a_717_);
goto v___jp_719_;
}
}
else
{
lean_dec(v_val_728_);
lean_dec_ref(v_a_717_);
goto v___jp_719_;
}
}
else
{
lean_dec(v___x_727_);
lean_dec_ref(v_a_717_);
goto v___jp_719_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_a_717_);
v___x_781_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___boxed(lean_object* v_json_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_json_783_, v_a_784_);
lean_dec(v_json_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(lean_object* v_json_790_, lean_object* v_a_791_){
_start:
{
if (lean_obj_tag(v_json_790_) == 2)
{
lean_object* v_n_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_832_; 
v_n_796_ = lean_ctor_get(v_json_790_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_json_790_);
if (v_isSharedCheck_832_ == 0)
{
v___x_798_ = v_json_790_;
v_isShared_799_ = v_isSharedCheck_832_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_n_796_);
lean_dec(v_json_790_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_832_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_mantissa_800_; lean_object* v_exponent_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_831_; 
v_mantissa_800_ = lean_ctor_get(v_n_796_, 0);
v_exponent_801_ = lean_ctor_get(v_n_796_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_n_796_);
if (v_isSharedCheck_831_ == 0)
{
v___x_803_ = v_n_796_;
v_isShared_804_ = v_isSharedCheck_831_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_exponent_801_);
lean_inc(v_mantissa_800_);
lean_dec(v_n_796_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_831_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_natZero_805_; lean_object* v_intZero_806_; uint8_t v_isNeg_807_; 
v_natZero_805_ = lean_unsigned_to_nat(0u);
v_intZero_806_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_807_ = lean_int_dec_lt(v_mantissa_800_, v_intZero_806_);
if (v_isNeg_807_ == 0)
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_eq(v_exponent_801_, v_natZero_805_);
lean_dec(v_exponent_801_);
if (v___x_808_ == 0)
{
lean_del_object(v___x_803_);
lean_dec(v_mantissa_800_);
lean_del_object(v___x_798_);
lean_dec_ref(v_a_791_);
goto v___jp_793_;
}
else
{
lean_object* v_levelMap_809_; lean_object* v_a_810_; lean_object* v___x_811_; 
v_levelMap_809_ = lean_ctor_get(v_a_791_, 2);
v_a_810_ = lean_nat_abs(v_mantissa_800_);
lean_dec(v_mantissa_800_);
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_809_, v_a_810_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_810_);
lean_del_object(v___x_798_);
v_val_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_823_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_Level_succ___override(v_val_812_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_a_791_);
lean_ctor_set(v___x_803_, 0, v___x_816_);
v___x_818_ = v___x_803_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_791_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_818_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v___x_811_);
lean_del_object(v___x_803_);
lean_dec_ref(v_a_791_);
v___x_824_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_825_ = l_Nat_reprFast(v_a_810_);
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
lean_dec_ref(v___x_825_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 18);
lean_ctor_set(v___x_798_, 0, v___x_826_);
v___x_828_ = v___x_798_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
}
else
{
lean_del_object(v___x_803_);
lean_dec(v_exponent_801_);
lean_dec(v_mantissa_800_);
lean_del_object(v___x_798_);
lean_dec_ref(v_a_791_);
goto v___jp_793_;
}
}
}
}
else
{
lean_dec_ref(v_a_791_);
lean_dec(v_json_790_);
goto v___jp_793_;
}
v___jp_793_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1));
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___boxed(lean_object* v_json_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_json_833_, v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(lean_object* v_json_840_, lean_object* v_a_841_){
_start:
{
if (lean_obj_tag(v_json_840_) == 4)
{
lean_object* v_elems_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_elems_846_ = lean_ctor_get(v_json_840_, 0);
v___x_847_ = lean_array_get_size(v_elems_846_);
v___x_848_ = lean_unsigned_to_nat(2u);
v___x_849_ = lean_nat_dec_eq(v___x_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_array_fget(v_elems_846_, v___x_850_);
if (lean_obj_tag(v___x_851_) == 2)
{
lean_object* v_n_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_916_; 
v_n_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_916_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_916_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_n_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_916_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_mantissa_856_; lean_object* v_exponent_857_; lean_object* v_intZero_858_; uint8_t v_isNeg_859_; 
v_mantissa_856_ = lean_ctor_get(v_n_852_, 0);
lean_inc(v_mantissa_856_);
v_exponent_857_ = lean_ctor_get(v_n_852_, 1);
lean_inc(v_exponent_857_);
lean_dec_ref(v_n_852_);
v_intZero_858_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_859_ = lean_int_dec_lt(v_mantissa_856_, v_intZero_858_);
if (v_isNeg_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_eq(v_exponent_857_, v___x_850_);
lean_dec(v_exponent_857_);
if (v___x_860_ == 0)
{
lean_dec(v_mantissa_856_);
lean_del_object(v___x_854_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_array_fget(v_elems_846_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 2)
{
lean_object* v_n_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_915_; 
v_n_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_915_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_915_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_n_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_915_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_mantissa_867_; lean_object* v_exponent_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_914_; 
v_mantissa_867_ = lean_ctor_get(v_n_863_, 0);
v_exponent_868_ = lean_ctor_get(v_n_863_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_n_863_);
if (v_isSharedCheck_914_ == 0)
{
v___x_870_ = v_n_863_;
v_isShared_871_ = v_isSharedCheck_914_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_exponent_868_);
lean_inc(v_mantissa_867_);
lean_dec(v_n_863_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_914_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v_isNeg_872_; 
v_isNeg_872_ = lean_int_dec_lt(v_mantissa_867_, v_intZero_858_);
if (v_isNeg_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_eq(v_exponent_868_, v___x_850_);
lean_dec(v_exponent_868_);
if (v___x_873_ == 0)
{
lean_del_object(v___x_870_);
lean_dec(v_mantissa_867_);
lean_del_object(v___x_865_);
lean_dec(v_mantissa_856_);
lean_del_object(v___x_854_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
else
{
lean_object* v_levelMap_874_; lean_object* v_a_875_; lean_object* v___x_876_; 
v_levelMap_874_ = lean_ctor_get(v_a_841_, 2);
v_a_875_ = lean_nat_abs(v_mantissa_856_);
lean_dec(v_mantissa_856_);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_874_, v_a_875_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_a_875_);
lean_del_object(v___x_854_);
v_val_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_904_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_904_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_904_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_nat_abs(v_mantissa_867_);
lean_dec(v_mantissa_867_);
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_874_, v_a_881_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_a_881_);
lean_del_object(v___x_879_);
lean_del_object(v___x_865_);
v_val_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_894_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_Level_max___override(v_val_877_, v_val_883_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_a_841_);
lean_ctor_set(v___x_870_, 0, v___x_887_);
v___x_889_ = v___x_870_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_a_841_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 0);
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v___x_882_);
lean_dec(v_val_877_);
lean_del_object(v___x_870_);
lean_dec_ref(v_a_841_);
v___x_895_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_896_ = l_Nat_reprFast(v_a_881_);
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
lean_dec_ref(v___x_896_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 18);
lean_ctor_set(v___x_879_, 0, v___x_897_);
v___x_899_ = v___x_879_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 1);
lean_ctor_set(v___x_865_, 0, v___x_899_);
v___x_901_ = v___x_865_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v___x_876_);
lean_del_object(v___x_870_);
lean_dec(v_mantissa_867_);
lean_dec_ref(v_a_841_);
v___x_905_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_906_ = l_Nat_reprFast(v_a_875_);
v___x_907_ = lean_string_append(v___x_905_, v___x_906_);
lean_dec_ref(v___x_906_);
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 18);
lean_ctor_set(v___x_865_, 0, v___x_907_);
v___x_909_ = v___x_865_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 1);
lean_ctor_set(v___x_854_, 0, v___x_909_);
v___x_911_ = v___x_854_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
else
{
lean_del_object(v___x_870_);
lean_dec(v_exponent_868_);
lean_dec(v_mantissa_867_);
lean_del_object(v___x_865_);
lean_dec(v_mantissa_856_);
lean_del_object(v___x_854_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
}
}
}
else
{
lean_dec(v___x_862_);
lean_dec(v_mantissa_856_);
lean_del_object(v___x_854_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
}
}
else
{
lean_dec(v_exponent_857_);
lean_dec(v_mantissa_856_);
lean_del_object(v___x_854_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
}
}
else
{
lean_dec(v___x_851_);
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
}
}
else
{
lean_dec_ref(v_a_841_);
goto v___jp_843_;
}
v___jp_843_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1));
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___boxed(lean_object* v_json_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_json_917_, v_a_918_);
lean_dec(v_json_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(lean_object* v_json_924_, lean_object* v_a_925_){
_start:
{
if (lean_obj_tag(v_json_924_) == 4)
{
lean_object* v_elems_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_elems_930_ = lean_ctor_get(v_json_924_, 0);
v___x_931_ = lean_array_get_size(v_elems_930_);
v___x_932_ = lean_unsigned_to_nat(2u);
v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_array_fget(v_elems_930_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 2)
{
lean_object* v_n_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1000_; 
v_n_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_1000_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_n_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1000_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_mantissa_940_; lean_object* v_exponent_941_; lean_object* v_intZero_942_; uint8_t v_isNeg_943_; 
v_mantissa_940_ = lean_ctor_get(v_n_936_, 0);
lean_inc(v_mantissa_940_);
v_exponent_941_ = lean_ctor_get(v_n_936_, 1);
lean_inc(v_exponent_941_);
lean_dec_ref(v_n_936_);
v_intZero_942_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_943_ = lean_int_dec_lt(v_mantissa_940_, v_intZero_942_);
if (v_isNeg_943_ == 0)
{
uint8_t v___x_944_; 
v___x_944_ = lean_nat_dec_eq(v_exponent_941_, v___x_934_);
lean_dec(v_exponent_941_);
if (v___x_944_ == 0)
{
lean_dec(v_mantissa_940_);
lean_del_object(v___x_938_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_array_fget(v_elems_930_, v___x_945_);
if (lean_obj_tag(v___x_946_) == 2)
{
lean_object* v_n_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_999_; 
v_n_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_999_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_999_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_n_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_999_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_mantissa_951_; lean_object* v_exponent_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_998_; 
v_mantissa_951_ = lean_ctor_get(v_n_947_, 0);
v_exponent_952_ = lean_ctor_get(v_n_947_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_n_947_);
if (v_isSharedCheck_998_ == 0)
{
v___x_954_ = v_n_947_;
v_isShared_955_ = v_isSharedCheck_998_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_exponent_952_);
lean_inc(v_mantissa_951_);
lean_dec(v_n_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_998_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
uint8_t v_isNeg_956_; 
v_isNeg_956_ = lean_int_dec_lt(v_mantissa_951_, v_intZero_942_);
if (v_isNeg_956_ == 0)
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_eq(v_exponent_952_, v___x_934_);
lean_dec(v_exponent_952_);
if (v___x_957_ == 0)
{
lean_del_object(v___x_954_);
lean_dec(v_mantissa_951_);
lean_del_object(v___x_949_);
lean_dec(v_mantissa_940_);
lean_del_object(v___x_938_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
else
{
lean_object* v_levelMap_958_; lean_object* v_a_959_; lean_object* v___x_960_; 
v_levelMap_958_ = lean_ctor_get(v_a_925_, 2);
v_a_959_ = lean_nat_abs(v_mantissa_940_);
lean_dec(v_mantissa_940_);
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_958_, v_a_959_);
if (lean_obj_tag(v___x_960_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_959_);
lean_del_object(v___x_938_);
v_val_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_988_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_nat_abs(v_mantissa_951_);
lean_dec(v_mantissa_951_);
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_958_, v_a_965_);
if (lean_obj_tag(v___x_966_) == 1)
{
lean_object* v_val_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_965_);
lean_del_object(v___x_963_);
lean_del_object(v___x_949_);
v_val_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_978_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_val_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Lean_Level_imax___override(v_val_961_, v_val_967_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_a_925_);
lean_ctor_set(v___x_954_, 0, v___x_971_);
v___x_973_ = v___x_954_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_a_925_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 0);
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
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
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
lean_dec(v___x_966_);
lean_dec(v_val_961_);
lean_del_object(v___x_954_);
lean_dec_ref(v_a_925_);
v___x_979_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_980_ = l_Nat_reprFast(v_a_965_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 18);
lean_ctor_set(v___x_963_, 0, v___x_981_);
v___x_983_ = v___x_963_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 1);
lean_ctor_set(v___x_949_, 0, v___x_983_);
v___x_985_ = v___x_949_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v___x_960_);
lean_del_object(v___x_954_);
lean_dec(v_mantissa_951_);
lean_dec_ref(v_a_925_);
v___x_989_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_990_ = l_Nat_reprFast(v_a_959_);
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
lean_dec_ref(v___x_990_);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 18);
lean_ctor_set(v___x_949_, 0, v___x_991_);
v___x_993_ = v___x_949_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 0, v___x_993_);
v___x_995_ = v___x_938_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
else
{
lean_del_object(v___x_954_);
lean_dec(v_exponent_952_);
lean_dec(v_mantissa_951_);
lean_del_object(v___x_949_);
lean_dec(v_mantissa_940_);
lean_del_object(v___x_938_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
}
}
}
else
{
lean_dec(v___x_946_);
lean_dec(v_mantissa_940_);
lean_del_object(v___x_938_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
}
}
else
{
lean_dec(v_exponent_941_);
lean_dec(v_mantissa_940_);
lean_del_object(v___x_938_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
}
}
else
{
lean_dec(v___x_935_);
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
}
}
else
{
lean_dec_ref(v_a_925_);
goto v___jp_927_;
}
v___jp_927_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1));
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___boxed(lean_object* v_json_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_json_1001_, v_a_1002_);
lean_dec(v_json_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(lean_object* v_json_1008_, lean_object* v_a_1009_){
_start:
{
if (lean_obj_tag(v_json_1008_) == 2)
{
lean_object* v_n_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1050_; 
v_n_1014_ = lean_ctor_get(v_json_1008_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_json_1008_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1016_ = v_json_1008_;
v_isShared_1017_ = v_isSharedCheck_1050_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_n_1014_);
lean_dec(v_json_1008_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1050_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_mantissa_1018_; lean_object* v_exponent_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1049_; 
v_mantissa_1018_ = lean_ctor_get(v_n_1014_, 0);
v_exponent_1019_ = lean_ctor_get(v_n_1014_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_n_1014_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1021_ = v_n_1014_;
v_isShared_1022_ = v_isSharedCheck_1049_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_exponent_1019_);
lean_inc(v_mantissa_1018_);
lean_dec(v_n_1014_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1049_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_natZero_1023_; lean_object* v_intZero_1024_; uint8_t v_isNeg_1025_; 
v_natZero_1023_ = lean_unsigned_to_nat(0u);
v_intZero_1024_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1025_ = lean_int_dec_lt(v_mantissa_1018_, v_intZero_1024_);
if (v_isNeg_1025_ == 0)
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_nat_dec_eq(v_exponent_1019_, v_natZero_1023_);
lean_dec(v_exponent_1019_);
if (v___x_1026_ == 0)
{
lean_del_object(v___x_1021_);
lean_dec(v_mantissa_1018_);
lean_del_object(v___x_1016_);
lean_dec_ref(v_a_1009_);
goto v___jp_1011_;
}
else
{
lean_object* v_nameMap_1027_; lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_nameMap_1027_ = lean_ctor_get(v_a_1009_, 1);
v_a_1028_ = lean_nat_abs(v_mantissa_1018_);
lean_dec(v_mantissa_1018_);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_1028_);
lean_del_object(v___x_1016_);
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = l_Lean_Level_param___override(v_val_1030_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_a_1009_);
lean_ctor_set(v___x_1021_, 0, v___x_1034_);
v___x_1036_ = v___x_1021_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1009_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v___x_1029_);
lean_del_object(v___x_1021_);
lean_dec_ref(v_a_1009_);
v___x_1042_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1043_ = l_Nat_reprFast(v_a_1028_);
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
lean_dec_ref(v___x_1043_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 18);
lean_ctor_set(v___x_1016_, 0, v___x_1044_);
v___x_1046_ = v___x_1016_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
}
else
{
lean_del_object(v___x_1021_);
lean_dec(v_exponent_1019_);
lean_dec(v_mantissa_1018_);
lean_del_object(v___x_1016_);
lean_dec_ref(v_a_1009_);
goto v___jp_1011_;
}
}
}
}
else
{
lean_dec_ref(v_a_1009_);
lean_dec(v_json_1008_);
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1));
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___boxed(lean_object* v_json_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_json_1051_, v_a_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(lean_object* v_json_1058_, lean_object* v_a_1059_){
_start:
{
if (lean_obj_tag(v_json_1058_) == 2)
{
lean_object* v_n_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1086_; 
v_n_1064_ = lean_ctor_get(v_json_1058_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_json_1058_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1066_ = v_json_1058_;
v_isShared_1067_ = v_isSharedCheck_1086_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_n_1064_);
lean_dec(v_json_1058_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1086_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_mantissa_1068_; lean_object* v_exponent_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1085_; 
v_mantissa_1068_ = lean_ctor_get(v_n_1064_, 0);
v_exponent_1069_ = lean_ctor_get(v_n_1064_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_n_1064_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1071_ = v_n_1064_;
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_exponent_1069_);
lean_inc(v_mantissa_1068_);
lean_dec(v_n_1064_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_natZero_1073_; lean_object* v_intZero_1074_; uint8_t v_isNeg_1075_; 
v_natZero_1073_ = lean_unsigned_to_nat(0u);
v_intZero_1074_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1075_ = lean_int_dec_lt(v_mantissa_1068_, v_intZero_1074_);
if (v_isNeg_1075_ == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_nat_dec_eq(v_exponent_1069_, v_natZero_1073_);
lean_dec(v_exponent_1069_);
if (v___x_1076_ == 0)
{
lean_del_object(v___x_1071_);
lean_dec(v_mantissa_1068_);
lean_del_object(v___x_1066_);
lean_dec_ref(v_a_1059_);
goto v___jp_1061_;
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_a_1077_ = lean_nat_abs(v_mantissa_1068_);
lean_dec(v_mantissa_1068_);
v___x_1078_ = l_Lean_Expr_bvar___override(v_a_1077_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_a_1059_);
lean_ctor_set(v___x_1071_, 0, v___x_1078_);
v___x_1080_ = v___x_1071_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1059_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1080_);
v___x_1082_ = v___x_1066_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_del_object(v___x_1071_);
lean_dec(v_exponent_1069_);
lean_dec(v_mantissa_1068_);
lean_del_object(v___x_1066_);
lean_dec_ref(v_a_1059_);
goto v___jp_1061_;
}
}
}
}
else
{
lean_dec_ref(v_a_1059_);
lean_dec(v_json_1058_);
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1));
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___boxed(lean_object* v_json_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_json_1087_, v_a_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(lean_object* v_json_1094_, lean_object* v_a_1095_){
_start:
{
if (lean_obj_tag(v_json_1094_) == 2)
{
lean_object* v_n_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1136_; 
v_n_1100_ = lean_ctor_get(v_json_1094_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_json_1094_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1102_ = v_json_1094_;
v_isShared_1103_ = v_isSharedCheck_1136_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_n_1100_);
lean_dec(v_json_1094_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1136_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_mantissa_1104_; lean_object* v_exponent_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1135_; 
v_mantissa_1104_ = lean_ctor_get(v_n_1100_, 0);
v_exponent_1105_ = lean_ctor_get(v_n_1100_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_n_1100_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1107_ = v_n_1100_;
v_isShared_1108_ = v_isSharedCheck_1135_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_exponent_1105_);
lean_inc(v_mantissa_1104_);
lean_dec(v_n_1100_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1135_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_natZero_1109_; lean_object* v_intZero_1110_; uint8_t v_isNeg_1111_; 
v_natZero_1109_ = lean_unsigned_to_nat(0u);
v_intZero_1110_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1111_ = lean_int_dec_lt(v_mantissa_1104_, v_intZero_1110_);
if (v_isNeg_1111_ == 0)
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_nat_dec_eq(v_exponent_1105_, v_natZero_1109_);
lean_dec(v_exponent_1105_);
if (v___x_1112_ == 0)
{
lean_del_object(v___x_1107_);
lean_dec(v_mantissa_1104_);
lean_del_object(v___x_1102_);
lean_dec_ref(v_a_1095_);
goto v___jp_1097_;
}
else
{
lean_object* v_levelMap_1113_; lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_levelMap_1113_ = lean_ctor_get(v_a_1095_, 2);
v_a_1114_ = lean_nat_abs(v_mantissa_1104_);
lean_dec(v_mantissa_1104_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1115_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1114_);
lean_del_object(v___x_1102_);
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_val_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Expr_sort___override(v_val_1116_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v_a_1095_);
lean_ctor_set(v___x_1107_, 0, v___x_1120_);
v___x_1122_ = v___x_1107_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1095_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1122_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v___x_1115_);
lean_del_object(v___x_1107_);
lean_dec_ref(v_a_1095_);
v___x_1128_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1129_ = l_Nat_reprFast(v_a_1114_);
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 18);
lean_ctor_set(v___x_1102_, 0, v___x_1130_);
v___x_1132_ = v___x_1102_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
else
{
lean_del_object(v___x_1107_);
lean_dec(v_exponent_1105_);
lean_dec(v_mantissa_1104_);
lean_del_object(v___x_1102_);
lean_dec_ref(v_a_1095_);
goto v___jp_1097_;
}
}
}
}
else
{
lean_dec_ref(v_a_1095_);
lean_dec(v_json_1094_);
goto v___jp_1097_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1));
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___boxed(lean_object* v_json_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_json_1137_, v_a_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(size_t v_sz_1144_, size_t v_i_1145_, lean_object* v_bs_1146_, lean_object* v___y_1147_){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_usize_dec_lt(v_i_1145_, v_sz_1144_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_bs_1146_);
lean_ctor_set(v___x_1153_, 1, v___y_1147_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v_v_1155_; 
v_v_1155_ = lean_array_uget(v_bs_1146_, v_i_1145_);
if (lean_obj_tag(v_v_1155_) == 2)
{
lean_object* v_n_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1182_; 
v_n_1156_ = lean_ctor_get(v_v_1155_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_v_1155_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1158_ = v_v_1155_;
v_isShared_1159_ = v_isSharedCheck_1182_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_n_1156_);
lean_dec(v_v_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1182_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_mantissa_1160_; lean_object* v_exponent_1161_; lean_object* v_natZero_1162_; lean_object* v_intZero_1163_; uint8_t v_isNeg_1164_; 
v_mantissa_1160_ = lean_ctor_get(v_n_1156_, 0);
lean_inc(v_mantissa_1160_);
v_exponent_1161_ = lean_ctor_get(v_n_1156_, 1);
lean_inc(v_exponent_1161_);
lean_dec_ref(v_n_1156_);
v_natZero_1162_ = lean_unsigned_to_nat(0u);
v_intZero_1163_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1164_ = lean_int_dec_lt(v_mantissa_1160_, v_intZero_1163_);
if (v_isNeg_1164_ == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_nat_dec_eq(v_exponent_1161_, v_natZero_1162_);
lean_dec(v_exponent_1161_);
if (v___x_1165_ == 0)
{
lean_dec(v_mantissa_1160_);
lean_del_object(v___x_1158_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_bs_1146_);
goto v___jp_1149_;
}
else
{
lean_object* v_levelMap_1166_; lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_levelMap_1166_ = lean_ctor_get(v___y_1147_, 2);
v_a_1167_ = lean_nat_abs(v_mantissa_1160_);
lean_dec(v_mantissa_1160_);
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1168_) == 1)
{
lean_object* v_val_1169_; lean_object* v_bs_x27_1170_; size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_a_1167_);
lean_del_object(v___x_1158_);
v_val_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_bs_x27_1170_ = lean_array_uset(v_bs_1146_, v_i_1145_, v_natZero_1162_);
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1145_, v___x_1171_);
v___x_1173_ = lean_array_uset(v_bs_x27_1170_, v_i_1145_, v_val_1169_);
v_i_1145_ = v___x_1172_;
v_bs_1146_ = v___x_1173_;
goto _start;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec(v___x_1168_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_bs_1146_);
v___x_1175_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1176_ = l_Nat_reprFast(v_a_1167_);
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
lean_dec_ref(v___x_1176_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 18);
lean_ctor_set(v___x_1158_, 0, v___x_1177_);
v___x_1179_ = v___x_1158_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
}
else
{
lean_dec(v_exponent_1161_);
lean_dec(v_mantissa_1160_);
lean_del_object(v___x_1158_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_bs_1146_);
goto v___jp_1149_;
}
}
}
else
{
lean_dec(v_v_1155_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_bs_1146_);
goto v___jp_1149_;
}
}
v___jp_1149_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___boxed(lean_object* v_sz_1183_, lean_object* v_i_1184_, lean_object* v_bs_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
size_t v_sz_boxed_1188_; size_t v_i_boxed_1189_; lean_object* v_res_1190_; 
v_sz_boxed_1188_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1189_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_boxed_1188_, v_i_boxed_1189_, v_bs_1185_, v___y_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(lean_object* v_json_1193_, lean_object* v_a_1194_){
_start:
{
if (lean_obj_tag(v_json_1193_) == 5)
{
lean_object* v_kvPairs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_kvPairs_1202_ = lean_ctor_get(v_json_1193_, 0);
v___x_1203_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1202_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 1)
{
lean_object* v_val_1205_; 
v_val_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v___x_1204_, 1);
if (lean_obj_tag(v_val_1205_) == 2)
{
lean_object* v_n_1206_; lean_object* v_mantissa_1207_; lean_object* v_exponent_1208_; lean_object* v_natZero_1209_; lean_object* v_intZero_1210_; uint8_t v_isNeg_1211_; 
v_n_1206_ = lean_ctor_get(v_val_1205_, 0);
lean_inc_ref(v_n_1206_);
lean_dec_ref_known(v_val_1205_, 1);
v_mantissa_1207_ = lean_ctor_get(v_n_1206_, 0);
lean_inc(v_mantissa_1207_);
v_exponent_1208_ = lean_ctor_get(v_n_1206_, 1);
lean_inc(v_exponent_1208_);
lean_dec_ref(v_n_1206_);
v_natZero_1209_ = lean_unsigned_to_nat(0u);
v_intZero_1210_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1211_ = lean_int_dec_lt(v_mantissa_1207_, v_intZero_1210_);
if (v_isNeg_1211_ == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_eq(v_exponent_1208_, v_natZero_1209_);
lean_dec(v_exponent_1208_);
if (v___x_1212_ == 0)
{
lean_dec(v_mantissa_1207_);
lean_dec_ref(v_a_1194_);
goto v___jp_1196_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1));
v___x_1214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1202_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1267_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1267_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1267_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
if (lean_obj_tag(v_val_1215_) == 4)
{
lean_object* v_elems_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1266_; 
v_elems_1219_ = lean_ctor_get(v_val_1215_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_val_1215_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1221_ = v_val_1215_;
v_isShared_1222_ = v_isSharedCheck_1266_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_elems_1219_);
lean_dec(v_val_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1266_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_nameMap_1223_; lean_object* v_a_1224_; lean_object* v___x_1225_; 
v_nameMap_1223_ = lean_ctor_get(v_a_1194_, 1);
v_a_1224_ = lean_nat_abs(v_mantissa_1207_);
lean_dec(v_mantissa_1207_);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1223_, v_a_1224_);
if (lean_obj_tag(v___x_1225_) == 1)
{
lean_object* v_val_1226_; size_t v_sz_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
lean_dec(v_a_1224_);
lean_del_object(v___x_1221_);
lean_del_object(v___x_1217_);
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_sz_1227_ = lean_array_size(v_elems_1219_);
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_1227_, v___x_1228_, v_elems_1219_, v_a_1194_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1248_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1247_; 
v_fst_1234_ = lean_ctor_get(v_a_1230_, 0);
v_snd_1235_ = lean_ctor_get(v_a_1230_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1230_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1237_ = v_a_1230_;
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
lean_dec(v_a_1230_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1239_ = lean_array_to_list(v_fst_1234_);
v___x_1240_ = l_Lean_Expr_const___override(v_val_1226_, v___x_1239_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_snd_1235_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1242_);
v___x_1244_ = v___x_1232_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_val_1226_);
v_a_1249_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1229_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1229_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec(v___x_1225_);
lean_dec_ref(v_elems_1219_);
lean_dec_ref(v_a_1194_);
v___x_1257_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1258_ = l_Nat_reprFast(v_a_1224_);
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
lean_dec_ref(v___x_1258_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 18);
lean_ctor_set(v___x_1221_, 0, v___x_1259_);
v___x_1261_ = v___x_1221_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1261_);
v___x_1263_ = v___x_1217_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_del_object(v___x_1217_);
lean_dec(v_val_1215_);
lean_dec(v_mantissa_1207_);
lean_dec_ref(v_a_1194_);
goto v___jp_1199_;
}
}
}
else
{
lean_dec(v___x_1214_);
lean_dec(v_mantissa_1207_);
lean_dec_ref(v_a_1194_);
goto v___jp_1199_;
}
}
}
else
{
lean_dec(v_exponent_1208_);
lean_dec(v_mantissa_1207_);
lean_dec_ref(v_a_1194_);
goto v___jp_1196_;
}
}
else
{
lean_dec(v_val_1205_);
lean_dec_ref(v_a_1194_);
goto v___jp_1196_;
}
}
else
{
lean_dec(v___x_1204_);
lean_dec_ref(v_a_1194_);
goto v___jp_1196_;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_a_1194_);
v___x_1268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
v___jp_1196_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
v___jp_1199_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___boxed(lean_object* v_json_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_json_1270_, v_a_1271_);
lean_dec(v_json_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(lean_object* v_json_1279_, lean_object* v_a_1280_){
_start:
{
if (lean_obj_tag(v_json_1279_) == 5)
{
lean_object* v_kvPairs_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_kvPairs_1288_ = lean_ctor_get(v_json_1279_, 0);
v___x_1289_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2));
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1288_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 1)
{
lean_object* v_val_1291_; 
v_val_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1290_, 1);
if (lean_obj_tag(v_val_1291_) == 2)
{
lean_object* v_n_1292_; lean_object* v_mantissa_1293_; lean_object* v_exponent_1294_; lean_object* v_natZero_1295_; lean_object* v_intZero_1296_; uint8_t v_isNeg_1297_; 
v_n_1292_ = lean_ctor_get(v_val_1291_, 0);
lean_inc_ref(v_n_1292_);
lean_dec_ref_known(v_val_1291_, 1);
v_mantissa_1293_ = lean_ctor_get(v_n_1292_, 0);
lean_inc(v_mantissa_1293_);
v_exponent_1294_ = lean_ctor_get(v_n_1292_, 1);
lean_inc(v_exponent_1294_);
lean_dec_ref(v_n_1292_);
v_natZero_1295_ = lean_unsigned_to_nat(0u);
v_intZero_1296_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1297_ = lean_int_dec_lt(v_mantissa_1293_, v_intZero_1296_);
if (v_isNeg_1297_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_eq(v_exponent_1294_, v_natZero_1295_);
lean_dec(v_exponent_1294_);
if (v___x_1298_ == 0)
{
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3));
v___x_1300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1288_, v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 1)
{
lean_object* v_val_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1358_; 
v_val_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1358_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_val_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1358_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
if (lean_obj_tag(v_val_1301_) == 2)
{
lean_object* v_n_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1357_; 
v_n_1305_ = lean_ctor_get(v_val_1301_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_val_1301_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1307_ = v_val_1301_;
v_isShared_1308_ = v_isSharedCheck_1357_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_n_1305_);
lean_dec(v_val_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1357_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_mantissa_1309_; lean_object* v_exponent_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1356_; 
v_mantissa_1309_ = lean_ctor_get(v_n_1305_, 0);
v_exponent_1310_ = lean_ctor_get(v_n_1305_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_n_1305_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1312_ = v_n_1305_;
v_isShared_1313_ = v_isSharedCheck_1356_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_exponent_1310_);
lean_inc(v_mantissa_1309_);
lean_dec(v_n_1305_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1356_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
uint8_t v_isNeg_1314_; 
v_isNeg_1314_ = lean_int_dec_lt(v_mantissa_1309_, v_intZero_1296_);
if (v_isNeg_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_eq(v_exponent_1310_, v_natZero_1295_);
lean_dec(v_exponent_1310_);
if (v___x_1315_ == 0)
{
lean_del_object(v___x_1312_);
lean_dec(v_mantissa_1309_);
lean_del_object(v___x_1307_);
lean_del_object(v___x_1303_);
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1285_;
}
else
{
lean_object* v_exprMap_1316_; lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_exprMap_1316_ = lean_ctor_get(v_a_1280_, 3);
v_a_1317_ = lean_nat_abs(v_mantissa_1293_);
lean_dec(v_mantissa_1293_);
v___x_1318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1318_) == 1)
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1317_);
lean_del_object(v___x_1303_);
v_val_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1346_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1346_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_nat_abs(v_mantissa_1309_);
lean_dec(v_mantissa_1309_);
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1316_, v_a_1323_);
if (lean_obj_tag(v___x_1324_) == 1)
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1323_);
lean_del_object(v___x_1321_);
lean_del_object(v___x_1307_);
v_val_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_Expr_app___override(v_val_1319_, v_val_1325_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v_a_1280_);
lean_ctor_set(v___x_1312_, 0, v___x_1329_);
v___x_1331_ = v___x_1312_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_a_1280_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1331_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v___x_1324_);
lean_dec(v_val_1319_);
lean_del_object(v___x_1312_);
lean_dec_ref(v_a_1280_);
v___x_1337_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1338_ = l_Nat_reprFast(v_a_1323_);
v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
lean_dec_ref(v___x_1338_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 18);
lean_ctor_set(v___x_1321_, 0, v___x_1339_);
v___x_1341_ = v___x_1321_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1341_);
v___x_1343_ = v___x_1307_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_dec(v___x_1318_);
lean_del_object(v___x_1312_);
lean_dec(v_mantissa_1309_);
lean_dec_ref(v_a_1280_);
v___x_1347_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1348_ = l_Nat_reprFast(v_a_1317_);
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
lean_dec_ref(v___x_1348_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 18);
lean_ctor_set(v___x_1307_, 0, v___x_1349_);
v___x_1351_ = v___x_1307_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1351_);
v___x_1353_ = v___x_1303_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_del_object(v___x_1312_);
lean_dec(v_exponent_1310_);
lean_dec(v_mantissa_1309_);
lean_del_object(v___x_1307_);
lean_del_object(v___x_1303_);
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1285_;
}
}
}
}
else
{
lean_del_object(v___x_1303_);
lean_dec(v_val_1301_);
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1285_;
}
}
}
else
{
lean_dec(v___x_1300_);
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1285_;
}
}
}
else
{
lean_dec(v_exponent_1294_);
lean_dec(v_mantissa_1293_);
lean_dec_ref(v_a_1280_);
goto v___jp_1282_;
}
}
else
{
lean_dec(v_val_1291_);
lean_dec_ref(v_a_1280_);
goto v___jp_1282_;
}
}
else
{
lean_dec(v___x_1290_);
lean_dec_ref(v_a_1280_);
goto v___jp_1282_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_a_1280_);
v___x_1359_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
v___jp_1285_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___boxed(lean_object* v_json_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_json_1361_, v_a_1362_);
lean_dec(v_json_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(lean_object* v_info_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0));
v___x_1374_ = lean_string_dec_eq(v_info_1370_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1));
v___x_1376_ = lean_string_dec_eq(v_info_1370_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2));
v___x_1378_ = lean_string_dec_eq(v_info_1370_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3));
v___x_1380_ = lean_string_dec_eq(v_info_1370_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v_a_1371_);
v___x_1381_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4));
v___x_1382_ = lean_string_append(v___x_1381_, v_info_1370_);
v___x_1383_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
else
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = 3;
v___x_1386_ = lean_box(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1371_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
else
{
uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1389_ = 2;
v___x_1390_ = lean_box(v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_a_1371_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
else
{
uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = 1;
v___x_1394_ = lean_box(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_a_1371_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
else
{
uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1397_ = 0;
v___x_1398_ = lean_box(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_a_1371_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___boxed(lean_object* v_info_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_info_1401_, v_a_1402_);
lean_dec_ref(v_info_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(lean_object* v_json_1411_, lean_object* v_a_1412_){
_start:
{
if (lean_obj_tag(v_json_1411_) == 5)
{
lean_object* v_kvPairs_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_kvPairs_1426_ = lean_ctor_get(v_json_1411_, 0);
v___x_1427_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1426_, v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 1)
{
lean_object* v_val_1429_; 
v_val_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1428_, 1);
if (lean_obj_tag(v_val_1429_) == 2)
{
lean_object* v_n_1430_; lean_object* v_mantissa_1431_; lean_object* v_exponent_1432_; lean_object* v_natZero_1433_; lean_object* v_intZero_1434_; uint8_t v_isNeg_1435_; 
v_n_1430_ = lean_ctor_get(v_val_1429_, 0);
lean_inc_ref(v_n_1430_);
lean_dec_ref_known(v_val_1429_, 1);
v_mantissa_1431_ = lean_ctor_get(v_n_1430_, 0);
lean_inc(v_mantissa_1431_);
v_exponent_1432_ = lean_ctor_get(v_n_1430_, 1);
lean_inc(v_exponent_1432_);
lean_dec_ref(v_n_1430_);
v_natZero_1433_ = lean_unsigned_to_nat(0u);
v_intZero_1434_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1435_ = lean_int_dec_lt(v_mantissa_1431_, v_intZero_1434_);
if (v_isNeg_1435_ == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_eq(v_exponent_1432_, v_natZero_1433_);
lean_dec(v_exponent_1432_);
if (v___x_1436_ == 0)
{
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1414_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1426_, v___x_1437_);
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1438_, 1);
if (lean_obj_tag(v_val_1439_) == 2)
{
lean_object* v_n_1440_; lean_object* v_mantissa_1441_; lean_object* v_exponent_1442_; uint8_t v_isNeg_1443_; 
v_n_1440_ = lean_ctor_get(v_val_1439_, 0);
lean_inc_ref(v_n_1440_);
lean_dec_ref_known(v_val_1439_, 1);
v_mantissa_1441_ = lean_ctor_get(v_n_1440_, 0);
lean_inc(v_mantissa_1441_);
v_exponent_1442_ = lean_ctor_get(v_n_1440_, 1);
lean_inc(v_exponent_1442_);
lean_dec_ref(v_n_1440_);
v_isNeg_1443_ = lean_int_dec_lt(v_mantissa_1441_, v_intZero_1434_);
if (v_isNeg_1443_ == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_nat_dec_eq(v_exponent_1442_, v_natZero_1433_);
lean_dec(v_exponent_1442_);
if (v___x_1444_ == 0)
{
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1417_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1426_, v___x_1445_);
if (lean_obj_tag(v___x_1446_) == 1)
{
lean_object* v_val_1447_; 
v_val_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v___x_1446_, 1);
if (lean_obj_tag(v_val_1447_) == 2)
{
lean_object* v_n_1448_; lean_object* v_mantissa_1449_; lean_object* v_exponent_1450_; uint8_t v_isNeg_1451_; 
v_n_1448_ = lean_ctor_get(v_val_1447_, 0);
lean_inc_ref(v_n_1448_);
lean_dec_ref_known(v_val_1447_, 1);
v_mantissa_1449_ = lean_ctor_get(v_n_1448_, 0);
lean_inc(v_mantissa_1449_);
v_exponent_1450_ = lean_ctor_get(v_n_1448_, 1);
lean_inc(v_exponent_1450_);
lean_dec_ref(v_n_1448_);
v_isNeg_1451_ = lean_int_dec_lt(v_mantissa_1449_, v_intZero_1434_);
if (v_isNeg_1451_ == 0)
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_nat_dec_eq(v_exponent_1450_, v_natZero_1433_);
lean_dec(v_exponent_1450_);
if (v___x_1452_ == 0)
{
lean_dec(v_mantissa_1449_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1420_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1426_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1538_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1538_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1538_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
if (lean_obj_tag(v_val_1455_) == 3)
{
lean_object* v_s_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1537_; 
v_s_1459_ = lean_ctor_get(v_val_1455_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_val_1455_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1461_ = v_val_1455_;
v_isShared_1462_ = v_isSharedCheck_1537_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_s_1459_);
lean_dec(v_val_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1537_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_nameMap_1463_; lean_object* v_exprMap_1464_; lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_nameMap_1463_ = lean_ctor_get(v_a_1412_, 1);
v_exprMap_1464_ = lean_ctor_get(v_a_1412_, 3);
v_a_1465_ = lean_nat_abs(v_mantissa_1431_);
lean_dec(v_mantissa_1431_);
v___x_1466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1463_, v_a_1465_);
if (lean_obj_tag(v___x_1466_) == 1)
{
lean_object* v_val_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1465_);
lean_del_object(v___x_1457_);
v_val_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1527_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_val_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1527_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_nat_abs(v_mantissa_1441_);
lean_dec(v_mantissa_1441_);
v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1464_, v_a_1471_);
if (lean_obj_tag(v___x_1472_) == 1)
{
lean_object* v_val_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1461_);
v_val_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1517_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_val_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1517_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_nat_abs(v_mantissa_1449_);
lean_dec(v_mantissa_1449_);
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1464_, v_a_1477_);
if (lean_obj_tag(v___x_1478_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1480_; 
lean_dec(v_a_1477_);
lean_del_object(v___x_1475_);
lean_del_object(v___x_1469_);
v_val_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1459_, v_a_1412_);
lean_dec_ref(v_s_1459_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1499_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1499_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1499_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1498_; 
v_fst_1485_ = lean_ctor_get(v_a_1481_, 0);
v_snd_1486_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1488_ = v_a_1481_;
v_isShared_1489_ = v_isSharedCheck_1498_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snd_1486_);
lean_inc(v_fst_1485_);
lean_dec(v_a_1481_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1498_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_unbox(v_fst_1485_);
lean_dec(v_fst_1485_);
v___x_1491_ = l_Lean_Expr_lam___override(v_val_1467_, v_val_1473_, v_val_1479_, v___x_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1486_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1493_);
v___x_1495_ = v___x_1483_;
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
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_val_1479_);
lean_dec(v_val_1473_);
lean_dec(v_val_1467_);
v_a_1500_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1480_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1480_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v___x_1478_);
lean_dec(v_val_1473_);
lean_dec(v_val_1467_);
lean_dec_ref(v_s_1459_);
lean_dec_ref(v_a_1412_);
v___x_1508_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1509_ = l_Nat_reprFast(v_a_1477_);
v___x_1510_ = lean_string_append(v___x_1508_, v___x_1509_);
lean_dec_ref(v___x_1509_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 18);
lean_ctor_set(v___x_1475_, 0, v___x_1510_);
v___x_1512_ = v___x_1475_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1512_);
v___x_1514_ = v___x_1469_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec(v___x_1472_);
lean_dec(v_val_1467_);
lean_dec_ref(v_s_1459_);
lean_dec(v_mantissa_1449_);
lean_dec_ref(v_a_1412_);
v___x_1518_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1519_ = l_Nat_reprFast(v_a_1471_);
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
lean_dec_ref(v___x_1519_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 18);
lean_ctor_set(v___x_1469_, 0, v___x_1520_);
v___x_1522_ = v___x_1469_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
lean_ctor_set(v___x_1461_, 0, v___x_1522_);
v___x_1524_ = v___x_1461_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
lean_dec(v___x_1466_);
lean_dec_ref(v_s_1459_);
lean_dec(v_mantissa_1449_);
lean_dec(v_mantissa_1441_);
lean_dec_ref(v_a_1412_);
v___x_1528_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1529_ = l_Nat_reprFast(v_a_1465_);
v___x_1530_ = lean_string_append(v___x_1528_, v___x_1529_);
lean_dec_ref(v___x_1529_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 18);
lean_ctor_set(v___x_1461_, 0, v___x_1530_);
v___x_1532_ = v___x_1461_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1532_);
v___x_1534_ = v___x_1457_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_del_object(v___x_1457_);
lean_dec(v_val_1455_);
lean_dec(v_mantissa_1449_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1423_;
}
}
}
else
{
lean_dec(v___x_1454_);
lean_dec(v_mantissa_1449_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1423_;
}
}
}
else
{
lean_dec(v_exponent_1450_);
lean_dec(v_mantissa_1449_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1420_;
}
}
else
{
lean_dec(v_val_1447_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1420_;
}
}
else
{
lean_dec(v___x_1446_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1420_;
}
}
}
else
{
lean_dec(v_exponent_1442_);
lean_dec(v_mantissa_1441_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1417_;
}
}
else
{
lean_dec(v_val_1439_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1417_;
}
}
else
{
lean_dec(v___x_1438_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1417_;
}
}
}
else
{
lean_dec(v_exponent_1432_);
lean_dec(v_mantissa_1431_);
lean_dec_ref(v_a_1412_);
goto v___jp_1414_;
}
}
else
{
lean_dec(v_val_1429_);
lean_dec_ref(v_a_1412_);
goto v___jp_1414_;
}
}
else
{
lean_dec(v___x_1428_);
lean_dec_ref(v_a_1412_);
goto v___jp_1414_;
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref(v_a_1412_);
v___x_1539_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
v___jp_1414_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
v___jp_1417_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
v___jp_1420_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
v___jp_1423_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___boxed(lean_object* v_json_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_json_1541_, v_a_1542_);
lean_dec(v_json_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(lean_object* v_json_1548_, lean_object* v_a_1549_){
_start:
{
if (lean_obj_tag(v_json_1548_) == 5)
{
lean_object* v_kvPairs_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_kvPairs_1563_ = lean_ctor_get(v_json_1548_, 0);
v___x_1564_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1563_, v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 1)
{
lean_object* v_val_1566_; 
v_val_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___x_1565_, 1);
if (lean_obj_tag(v_val_1566_) == 2)
{
lean_object* v_n_1567_; lean_object* v_mantissa_1568_; lean_object* v_exponent_1569_; lean_object* v_natZero_1570_; lean_object* v_intZero_1571_; uint8_t v_isNeg_1572_; 
v_n_1567_ = lean_ctor_get(v_val_1566_, 0);
lean_inc_ref(v_n_1567_);
lean_dec_ref_known(v_val_1566_, 1);
v_mantissa_1568_ = lean_ctor_get(v_n_1567_, 0);
lean_inc(v_mantissa_1568_);
v_exponent_1569_ = lean_ctor_get(v_n_1567_, 1);
lean_inc(v_exponent_1569_);
lean_dec_ref(v_n_1567_);
v_natZero_1570_ = lean_unsigned_to_nat(0u);
v_intZero_1571_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1572_ = lean_int_dec_lt(v_mantissa_1568_, v_intZero_1571_);
if (v_isNeg_1572_ == 0)
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_eq(v_exponent_1569_, v_natZero_1570_);
lean_dec(v_exponent_1569_);
if (v___x_1573_ == 0)
{
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1563_, v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 1)
{
lean_object* v_val_1576_; 
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v___x_1575_, 1);
if (lean_obj_tag(v_val_1576_) == 2)
{
lean_object* v_n_1577_; lean_object* v_mantissa_1578_; lean_object* v_exponent_1579_; uint8_t v_isNeg_1580_; 
v_n_1577_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_n_1577_);
lean_dec_ref_known(v_val_1576_, 1);
v_mantissa_1578_ = lean_ctor_get(v_n_1577_, 0);
lean_inc(v_mantissa_1578_);
v_exponent_1579_ = lean_ctor_get(v_n_1577_, 1);
lean_inc(v_exponent_1579_);
lean_dec_ref(v_n_1577_);
v_isNeg_1580_ = lean_int_dec_lt(v_mantissa_1578_, v_intZero_1571_);
if (v_isNeg_1580_ == 0)
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_eq(v_exponent_1579_, v_natZero_1570_);
lean_dec(v_exponent_1579_);
if (v___x_1581_ == 0)
{
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1583_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1563_, v___x_1582_);
if (lean_obj_tag(v___x_1583_) == 1)
{
lean_object* v_val_1584_; 
v_val_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v___x_1583_, 1);
if (lean_obj_tag(v_val_1584_) == 2)
{
lean_object* v_n_1585_; lean_object* v_mantissa_1586_; lean_object* v_exponent_1587_; uint8_t v_isNeg_1588_; 
v_n_1585_ = lean_ctor_get(v_val_1584_, 0);
lean_inc_ref(v_n_1585_);
lean_dec_ref_known(v_val_1584_, 1);
v_mantissa_1586_ = lean_ctor_get(v_n_1585_, 0);
lean_inc(v_mantissa_1586_);
v_exponent_1587_ = lean_ctor_get(v_n_1585_, 1);
lean_inc(v_exponent_1587_);
lean_dec_ref(v_n_1585_);
v_isNeg_1588_ = lean_int_dec_lt(v_mantissa_1586_, v_intZero_1571_);
if (v_isNeg_1588_ == 0)
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_nat_dec_eq(v_exponent_1587_, v_natZero_1570_);
lean_dec(v_exponent_1587_);
if (v___x_1589_ == 0)
{
lean_dec(v_mantissa_1586_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1557_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1563_, v___x_1590_);
if (lean_obj_tag(v___x_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1675_; 
v_val_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1675_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_val_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1675_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
if (lean_obj_tag(v_val_1592_) == 3)
{
lean_object* v_s_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1674_; 
v_s_1596_ = lean_ctor_get(v_val_1592_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_val_1592_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1598_ = v_val_1592_;
v_isShared_1599_ = v_isSharedCheck_1674_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_s_1596_);
lean_dec(v_val_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1674_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_nameMap_1600_; lean_object* v_exprMap_1601_; lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_nameMap_1600_ = lean_ctor_get(v_a_1549_, 1);
v_exprMap_1601_ = lean_ctor_get(v_a_1549_, 3);
v_a_1602_ = lean_nat_abs(v_mantissa_1568_);
lean_dec(v_mantissa_1568_);
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1600_, v_a_1602_);
if (lean_obj_tag(v___x_1603_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1602_);
lean_del_object(v___x_1594_);
v_val_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1664_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1664_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_nat_abs(v_mantissa_1578_);
lean_dec(v_mantissa_1578_);
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1601_, v_a_1608_);
if (lean_obj_tag(v___x_1609_) == 1)
{
lean_object* v_val_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1608_);
lean_del_object(v___x_1598_);
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1654_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_val_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1654_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_nat_abs(v_mantissa_1586_);
lean_dec(v_mantissa_1586_);
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1601_, v_a_1614_);
if (lean_obj_tag(v___x_1615_) == 1)
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
lean_dec(v_a_1614_);
lean_del_object(v___x_1612_);
lean_del_object(v___x_1606_);
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1596_, v_a_1549_);
lean_dec_ref(v_s_1596_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1636_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1636_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1636_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1635_; 
v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1625_ = v_a_1618_;
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_a_1618_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = lean_unbox(v_fst_1622_);
lean_dec(v_fst_1622_);
v___x_1628_ = l_Lean_Expr_forallE___override(v_val_1604_, v_val_1610_, v_val_1616_, v___x_1627_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_snd_1623_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1630_);
v___x_1632_ = v___x_1620_;
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
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_val_1616_);
lean_dec(v_val_1610_);
lean_dec(v_val_1604_);
v_a_1637_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1617_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1617_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_dec(v___x_1615_);
lean_dec(v_val_1610_);
lean_dec(v_val_1604_);
lean_dec_ref(v_s_1596_);
lean_dec_ref(v_a_1549_);
v___x_1645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1646_ = l_Nat_reprFast(v_a_1614_);
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
lean_dec_ref(v___x_1646_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 18);
lean_ctor_set(v___x_1612_, 0, v___x_1647_);
v___x_1649_ = v___x_1612_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1649_);
v___x_1651_ = v___x_1606_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v___x_1609_);
lean_dec(v_val_1604_);
lean_dec_ref(v_s_1596_);
lean_dec(v_mantissa_1586_);
lean_dec_ref(v_a_1549_);
v___x_1655_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1656_ = l_Nat_reprFast(v_a_1608_);
v___x_1657_ = lean_string_append(v___x_1655_, v___x_1656_);
lean_dec_ref(v___x_1656_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 18);
lean_ctor_set(v___x_1606_, 0, v___x_1657_);
v___x_1659_ = v___x_1606_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1659_);
v___x_1661_ = v___x_1598_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v___x_1603_);
lean_dec_ref(v_s_1596_);
lean_dec(v_mantissa_1586_);
lean_dec(v_mantissa_1578_);
lean_dec_ref(v_a_1549_);
v___x_1665_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1666_ = l_Nat_reprFast(v_a_1602_);
v___x_1667_ = lean_string_append(v___x_1665_, v___x_1666_);
lean_dec_ref(v___x_1666_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 18);
lean_ctor_set(v___x_1598_, 0, v___x_1667_);
v___x_1669_ = v___x_1598_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1669_);
v___x_1671_ = v___x_1594_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
else
{
lean_del_object(v___x_1594_);
lean_dec(v_val_1592_);
lean_dec(v_mantissa_1586_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1560_;
}
}
}
else
{
lean_dec(v___x_1591_);
lean_dec(v_mantissa_1586_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1560_;
}
}
}
else
{
lean_dec(v_exponent_1587_);
lean_dec(v_mantissa_1586_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1557_;
}
}
else
{
lean_dec(v_val_1584_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1557_;
}
}
else
{
lean_dec(v___x_1583_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1557_;
}
}
}
else
{
lean_dec(v_exponent_1579_);
lean_dec(v_mantissa_1578_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1554_;
}
}
else
{
lean_dec(v_val_1576_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1554_;
}
}
else
{
lean_dec(v___x_1575_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1554_;
}
}
}
else
{
lean_dec(v_exponent_1569_);
lean_dec(v_mantissa_1568_);
lean_dec_ref(v_a_1549_);
goto v___jp_1551_;
}
}
else
{
lean_dec(v_val_1566_);
lean_dec_ref(v_a_1549_);
goto v___jp_1551_;
}
}
else
{
lean_dec(v___x_1565_);
lean_dec_ref(v_a_1549_);
goto v___jp_1551_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_a_1549_);
v___x_1676_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___boxed(lean_object* v_json_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_json_1678_, v_a_1679_);
lean_dec(v_json_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(lean_object* v_json_1687_, lean_object* v_a_1688_){
_start:
{
if (lean_obj_tag(v_json_1687_) == 5)
{
lean_object* v_kvPairs_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_kvPairs_1705_ = lean_ctor_get(v_json_1687_, 0);
v___x_1706_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1707_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1705_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 1)
{
lean_object* v_val_1708_; 
v_val_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v___x_1707_, 1);
if (lean_obj_tag(v_val_1708_) == 2)
{
lean_object* v_n_1709_; lean_object* v_mantissa_1710_; lean_object* v_exponent_1711_; lean_object* v_natZero_1712_; lean_object* v_intZero_1713_; uint8_t v_isNeg_1714_; 
v_n_1709_ = lean_ctor_get(v_val_1708_, 0);
lean_inc_ref(v_n_1709_);
lean_dec_ref_known(v_val_1708_, 1);
v_mantissa_1710_ = lean_ctor_get(v_n_1709_, 0);
lean_inc(v_mantissa_1710_);
v_exponent_1711_ = lean_ctor_get(v_n_1709_, 1);
lean_inc(v_exponent_1711_);
lean_dec_ref(v_n_1709_);
v_natZero_1712_ = lean_unsigned_to_nat(0u);
v_intZero_1713_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1714_ = lean_int_dec_lt(v_mantissa_1710_, v_intZero_1713_);
if (v_isNeg_1714_ == 0)
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_nat_dec_eq(v_exponent_1711_, v_natZero_1712_);
lean_dec(v_exponent_1711_);
if (v___x_1715_ == 0)
{
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1690_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1705_, v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 1)
{
lean_object* v_val_1718_; 
v_val_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref_known(v___x_1717_, 1);
if (lean_obj_tag(v_val_1718_) == 2)
{
lean_object* v_n_1719_; lean_object* v_mantissa_1720_; lean_object* v_exponent_1721_; uint8_t v_isNeg_1722_; 
v_n_1719_ = lean_ctor_get(v_val_1718_, 0);
lean_inc_ref(v_n_1719_);
lean_dec_ref_known(v_val_1718_, 1);
v_mantissa_1720_ = lean_ctor_get(v_n_1719_, 0);
lean_inc(v_mantissa_1720_);
v_exponent_1721_ = lean_ctor_get(v_n_1719_, 1);
lean_inc(v_exponent_1721_);
lean_dec_ref(v_n_1719_);
v_isNeg_1722_ = lean_int_dec_lt(v_mantissa_1720_, v_intZero_1713_);
if (v_isNeg_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_eq(v_exponent_1721_, v_natZero_1712_);
lean_dec(v_exponent_1721_);
if (v___x_1723_ == 0)
{
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1693_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1705_, v___x_1724_);
if (lean_obj_tag(v___x_1725_) == 1)
{
lean_object* v_val_1726_; 
v_val_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1725_, 1);
if (lean_obj_tag(v_val_1726_) == 2)
{
lean_object* v_n_1727_; lean_object* v_mantissa_1728_; lean_object* v_exponent_1729_; uint8_t v_isNeg_1730_; 
v_n_1727_ = lean_ctor_get(v_val_1726_, 0);
lean_inc_ref(v_n_1727_);
lean_dec_ref_known(v_val_1726_, 1);
v_mantissa_1728_ = lean_ctor_get(v_n_1727_, 0);
lean_inc(v_mantissa_1728_);
v_exponent_1729_ = lean_ctor_get(v_n_1727_, 1);
lean_inc(v_exponent_1729_);
lean_dec_ref(v_n_1727_);
v_isNeg_1730_ = lean_int_dec_lt(v_mantissa_1728_, v_intZero_1713_);
if (v_isNeg_1730_ == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_eq(v_exponent_1729_, v_natZero_1712_);
lean_dec(v_exponent_1729_);
if (v___x_1731_ == 0)
{
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1696_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1705_, v___x_1732_);
if (lean_obj_tag(v___x_1733_) == 1)
{
lean_object* v_val_1734_; 
v_val_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_val_1734_);
lean_dec_ref_known(v___x_1733_, 1);
if (lean_obj_tag(v_val_1734_) == 2)
{
lean_object* v_n_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1828_; 
v_n_1735_ = lean_ctor_get(v_val_1734_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_val_1734_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1737_ = v_val_1734_;
v_isShared_1738_ = v_isSharedCheck_1828_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_n_1735_);
lean_dec(v_val_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1828_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_mantissa_1739_; lean_object* v_exponent_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1827_; 
v_mantissa_1739_ = lean_ctor_get(v_n_1735_, 0);
v_exponent_1740_ = lean_ctor_get(v_n_1735_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_n_1735_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1742_ = v_n_1735_;
v_isShared_1743_ = v_isSharedCheck_1827_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_exponent_1740_);
lean_inc(v_mantissa_1739_);
lean_dec(v_n_1735_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1827_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
uint8_t v_isNeg_1744_; 
v_isNeg_1744_ = lean_int_dec_lt(v_mantissa_1739_, v_intZero_1713_);
if (v_isNeg_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_eq(v_exponent_1740_, v_natZero_1712_);
lean_dec(v_exponent_1740_);
if (v___x_1745_ == 0)
{
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_del_object(v___x_1737_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1699_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3));
v___x_1747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1705_, v___x_1746_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1826_; 
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1826_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_val_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1826_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
if (lean_obj_tag(v_val_1748_) == 1)
{
uint8_t v_b_1752_; lean_object* v_nameMap_1753_; lean_object* v_exprMap_1754_; lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_b_1752_ = lean_ctor_get_uint8(v_val_1748_, 0);
lean_dec_ref_known(v_val_1748_, 0);
v_nameMap_1753_ = lean_ctor_get(v_a_1688_, 1);
v_exprMap_1754_ = lean_ctor_get(v_a_1688_, 3);
v_a_1755_ = lean_nat_abs(v_mantissa_1710_);
lean_dec(v_mantissa_1710_);
v___x_1756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1753_, v_a_1755_);
if (lean_obj_tag(v___x_1756_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1755_);
lean_del_object(v___x_1737_);
v_val_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1816_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1816_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_nat_abs(v_mantissa_1720_);
lean_dec(v_mantissa_1720_);
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1754_, v_a_1761_);
if (lean_obj_tag(v___x_1762_) == 1)
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1761_);
lean_del_object(v___x_1750_);
v_val_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1806_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1806_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_nat_abs(v_mantissa_1728_);
lean_dec(v_mantissa_1728_);
v___x_1768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1754_, v_a_1767_);
if (lean_obj_tag(v___x_1768_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_a_1767_);
lean_del_object(v___x_1759_);
v_val_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_val_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_nat_abs(v_mantissa_1739_);
lean_dec(v_mantissa_1739_);
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1754_, v_a_1773_);
if (lean_obj_tag(v___x_1774_) == 1)
{
lean_object* v_val_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_a_1773_);
lean_del_object(v___x_1771_);
lean_del_object(v___x_1765_);
v_val_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_val_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_Expr_letE___override(v_val_1757_, v_val_1763_, v_val_1769_, v_val_1775_, v_b_1752_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1688_);
lean_ctor_set(v___x_1742_, 0, v___x_1779_);
v___x_1781_ = v___x_1742_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_a_1688_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set_tag(v___x_1777_, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1781_);
v___x_1783_ = v___x_1777_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec(v___x_1774_);
lean_dec(v_val_1769_);
lean_dec(v_val_1763_);
lean_dec(v_val_1757_);
lean_del_object(v___x_1742_);
lean_dec_ref(v_a_1688_);
v___x_1787_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1788_ = l_Nat_reprFast(v_a_1773_);
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_dec_ref(v___x_1788_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 18);
lean_ctor_set(v___x_1771_, 0, v___x_1789_);
v___x_1791_ = v___x_1771_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1791_);
v___x_1793_ = v___x_1765_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_dec(v___x_1768_);
lean_dec(v_val_1763_);
lean_dec(v_val_1757_);
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_dec_ref(v_a_1688_);
v___x_1797_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1798_ = l_Nat_reprFast(v_a_1767_);
v___x_1799_ = lean_string_append(v___x_1797_, v___x_1798_);
lean_dec_ref(v___x_1798_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 18);
lean_ctor_set(v___x_1765_, 0, v___x_1799_);
v___x_1801_ = v___x_1765_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1801_);
v___x_1803_ = v___x_1759_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec(v___x_1762_);
lean_dec(v_val_1757_);
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_dec(v_mantissa_1728_);
lean_dec_ref(v_a_1688_);
v___x_1807_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1808_ = l_Nat_reprFast(v_a_1761_);
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
lean_dec_ref(v___x_1808_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 18);
lean_ctor_set(v___x_1759_, 0, v___x_1809_);
v___x_1811_ = v___x_1759_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1811_);
v___x_1813_ = v___x_1750_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec(v___x_1756_);
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec_ref(v_a_1688_);
v___x_1817_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1818_ = l_Nat_reprFast(v_a_1755_);
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
lean_dec_ref(v___x_1818_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set_tag(v___x_1750_, 18);
lean_ctor_set(v___x_1750_, 0, v___x_1819_);
v___x_1821_ = v___x_1750_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 1);
lean_ctor_set(v___x_1737_, 0, v___x_1821_);
v___x_1823_ = v___x_1737_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_del_object(v___x_1750_);
lean_dec(v_val_1748_);
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_del_object(v___x_1737_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1702_;
}
}
}
else
{
lean_dec(v___x_1747_);
lean_del_object(v___x_1742_);
lean_dec(v_mantissa_1739_);
lean_del_object(v___x_1737_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1702_;
}
}
}
else
{
lean_del_object(v___x_1742_);
lean_dec(v_exponent_1740_);
lean_dec(v_mantissa_1739_);
lean_del_object(v___x_1737_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1699_;
}
}
}
}
else
{
lean_dec(v_val_1734_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1699_;
}
}
else
{
lean_dec(v___x_1733_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1699_;
}
}
}
else
{
lean_dec(v_exponent_1729_);
lean_dec(v_mantissa_1728_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1696_;
}
}
else
{
lean_dec(v_val_1726_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1696_;
}
}
else
{
lean_dec(v___x_1725_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1696_;
}
}
}
else
{
lean_dec(v_exponent_1721_);
lean_dec(v_mantissa_1720_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1693_;
}
}
else
{
lean_dec(v_val_1718_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1693_;
}
}
else
{
lean_dec(v___x_1717_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1693_;
}
}
}
else
{
lean_dec(v_exponent_1711_);
lean_dec(v_mantissa_1710_);
lean_dec_ref(v_a_1688_);
goto v___jp_1690_;
}
}
else
{
lean_dec(v_val_1708_);
lean_dec_ref(v_a_1688_);
goto v___jp_1690_;
}
}
else
{
lean_dec(v___x_1707_);
lean_dec_ref(v_a_1688_);
goto v___jp_1690_;
}
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_a_1688_);
v___x_1829_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
v___jp_1690_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
v___jp_1693_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
return v___x_1698_;
}
v___jp_1699_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
v___jp_1702_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___boxed(lean_object* v_json_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_json_1831_, v_a_1832_);
lean_dec(v_json_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(lean_object* v_json_1841_, lean_object* v_a_1842_){
_start:
{
if (lean_obj_tag(v_json_1841_) == 5)
{
lean_object* v_kvPairs_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_kvPairs_1853_ = lean_ctor_get(v_json_1841_, 0);
v___x_1854_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2));
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1853_, v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 1)
{
lean_object* v_val_1856_; 
v_val_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v___x_1855_, 1);
if (lean_obj_tag(v_val_1856_) == 2)
{
lean_object* v_n_1857_; lean_object* v_mantissa_1858_; lean_object* v_exponent_1859_; lean_object* v_natZero_1860_; lean_object* v_intZero_1861_; uint8_t v_isNeg_1862_; 
v_n_1857_ = lean_ctor_get(v_val_1856_, 0);
lean_inc_ref(v_n_1857_);
lean_dec_ref_known(v_val_1856_, 1);
v_mantissa_1858_ = lean_ctor_get(v_n_1857_, 0);
lean_inc(v_mantissa_1858_);
v_exponent_1859_ = lean_ctor_get(v_n_1857_, 1);
lean_inc(v_exponent_1859_);
lean_dec_ref(v_n_1857_);
v_natZero_1860_ = lean_unsigned_to_nat(0u);
v_intZero_1861_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1862_ = lean_int_dec_lt(v_mantissa_1858_, v_intZero_1861_);
if (v_isNeg_1862_ == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_eq(v_exponent_1859_, v_natZero_1860_);
lean_dec(v_exponent_1859_);
if (v___x_1863_ == 0)
{
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1844_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3));
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1853_, v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v___x_1865_, 1);
if (lean_obj_tag(v_val_1866_) == 2)
{
lean_object* v_n_1867_; lean_object* v_mantissa_1868_; lean_object* v_exponent_1869_; uint8_t v_isNeg_1870_; 
v_n_1867_ = lean_ctor_get(v_val_1866_, 0);
lean_inc_ref(v_n_1867_);
lean_dec_ref_known(v_val_1866_, 1);
v_mantissa_1868_ = lean_ctor_get(v_n_1867_, 0);
lean_inc(v_mantissa_1868_);
v_exponent_1869_ = lean_ctor_get(v_n_1867_, 1);
lean_inc(v_exponent_1869_);
lean_dec_ref(v_n_1867_);
v_isNeg_1870_ = lean_int_dec_lt(v_mantissa_1868_, v_intZero_1861_);
if (v_isNeg_1870_ == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_nat_dec_eq(v_exponent_1869_, v_natZero_1860_);
lean_dec(v_exponent_1869_);
if (v___x_1871_ == 0)
{
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1847_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4));
v___x_1873_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1853_, v___x_1872_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1933_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1933_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_val_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1933_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
if (lean_obj_tag(v_val_1874_) == 2)
{
lean_object* v_n_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1932_; 
v_n_1878_ = lean_ctor_get(v_val_1874_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_val_1874_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1880_ = v_val_1874_;
v_isShared_1881_ = v_isSharedCheck_1932_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_n_1878_);
lean_dec(v_val_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1932_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_mantissa_1882_; lean_object* v_exponent_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1931_; 
v_mantissa_1882_ = lean_ctor_get(v_n_1878_, 0);
v_exponent_1883_ = lean_ctor_get(v_n_1878_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_n_1878_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1885_ = v_n_1878_;
v_isShared_1886_ = v_isSharedCheck_1931_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_exponent_1883_);
lean_inc(v_mantissa_1882_);
lean_dec(v_n_1878_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1931_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
uint8_t v_isNeg_1887_; 
v_isNeg_1887_ = lean_int_dec_lt(v_mantissa_1882_, v_intZero_1861_);
if (v_isNeg_1887_ == 0)
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_eq(v_exponent_1883_, v_natZero_1860_);
lean_dec(v_exponent_1883_);
if (v___x_1888_ == 0)
{
lean_del_object(v___x_1885_);
lean_dec(v_mantissa_1882_);
lean_del_object(v___x_1880_);
lean_del_object(v___x_1876_);
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1850_;
}
else
{
lean_object* v_nameMap_1889_; lean_object* v_exprMap_1890_; lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_nameMap_1889_ = lean_ctor_get(v_a_1842_, 1);
v_exprMap_1890_ = lean_ctor_get(v_a_1842_, 3);
v_a_1891_ = lean_nat_abs(v_mantissa_1858_);
lean_dec(v_mantissa_1858_);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1889_, v_a_1891_);
if (lean_obj_tag(v___x_1892_) == 1)
{
lean_object* v_val_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1891_);
lean_del_object(v___x_1876_);
v_val_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1921_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_val_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1921_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_nat_abs(v_mantissa_1882_);
lean_dec(v_mantissa_1882_);
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1890_, v_a_1897_);
if (lean_obj_tag(v___x_1898_) == 1)
{
lean_object* v_val_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1897_);
lean_del_object(v___x_1895_);
lean_del_object(v___x_1880_);
v_val_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1911_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_val_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1911_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v_a_1903_ = lean_nat_abs(v_mantissa_1868_);
lean_dec(v_mantissa_1868_);
v___x_1904_ = l_Lean_Expr_proj___override(v_val_1893_, v_a_1903_, v_val_1899_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_a_1842_);
lean_ctor_set(v___x_1885_, 0, v___x_1904_);
v___x_1906_ = v___x_1885_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1842_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1906_);
v___x_1908_ = v___x_1901_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v___x_1898_);
lean_dec(v_val_1893_);
lean_del_object(v___x_1885_);
lean_dec(v_mantissa_1868_);
lean_dec_ref(v_a_1842_);
v___x_1912_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1913_ = l_Nat_reprFast(v_a_1897_);
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
lean_dec_ref(v___x_1913_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 18);
lean_ctor_set(v___x_1895_, 0, v___x_1914_);
v___x_1916_ = v___x_1895_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 1);
lean_ctor_set(v___x_1880_, 0, v___x_1916_);
v___x_1918_ = v___x_1880_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec(v___x_1892_);
lean_del_object(v___x_1885_);
lean_dec(v_mantissa_1882_);
lean_dec(v_mantissa_1868_);
lean_dec_ref(v_a_1842_);
v___x_1922_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1923_ = l_Nat_reprFast(v_a_1891_);
v___x_1924_ = lean_string_append(v___x_1922_, v___x_1923_);
lean_dec_ref(v___x_1923_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 18);
lean_ctor_set(v___x_1880_, 0, v___x_1924_);
v___x_1926_ = v___x_1880_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1926_);
v___x_1928_ = v___x_1876_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
else
{
lean_del_object(v___x_1885_);
lean_dec(v_exponent_1883_);
lean_dec(v_mantissa_1882_);
lean_del_object(v___x_1880_);
lean_del_object(v___x_1876_);
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1850_;
}
}
}
}
else
{
lean_del_object(v___x_1876_);
lean_dec(v_val_1874_);
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1850_;
}
}
}
else
{
lean_dec(v___x_1873_);
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1850_;
}
}
}
else
{
lean_dec(v_exponent_1869_);
lean_dec(v_mantissa_1868_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1847_;
}
}
else
{
lean_dec(v_val_1866_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1847_;
}
}
else
{
lean_dec(v___x_1865_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1847_;
}
}
}
else
{
lean_dec(v_exponent_1859_);
lean_dec(v_mantissa_1858_);
lean_dec_ref(v_a_1842_);
goto v___jp_1844_;
}
}
else
{
lean_dec(v_val_1856_);
lean_dec_ref(v_a_1842_);
goto v___jp_1844_;
}
}
else
{
lean_dec(v___x_1855_);
lean_dec_ref(v_a_1842_);
goto v___jp_1844_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec_ref(v_a_1842_);
v___x_1934_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
v___jp_1844_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
v___jp_1847_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___boxed(lean_object* v_json_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_json_1936_, v_a_1937_);
lean_dec(v_json_1936_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(lean_object* v_json_1943_, lean_object* v_a_1944_){
_start:
{
if (lean_obj_tag(v_json_1943_) == 3)
{
lean_object* v_s_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1971_; 
v_s_1946_ = lean_ctor_get(v_json_1943_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_json_1943_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1948_ = v_json_1943_;
v_isShared_1949_ = v_isSharedCheck_1971_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_s_1946_);
lean_dec(v_json_1943_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1971_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_string_utf8_byte_size(v_s_1946_);
v___x_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1952_, 0, v_s_1946_);
lean_ctor_set(v___x_1952_, 1, v___x_1950_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
v___x_1953_ = l_String_Slice_toNat_x3f(v___x_1952_);
lean_dec_ref_known(v___x_1952_, 3);
if (lean_obj_tag(v___x_1953_) == 1)
{
lean_object* v_val_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1966_; 
v_val_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1966_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_val_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1966_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 0);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_val_1954_);
v___x_1959_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1960_ = l_Lean_Expr_lit___override(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_a_1944_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1961_);
v___x_1963_ = v___x_1948_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
lean_dec(v___x_1953_);
lean_dec_ref(v_a_1944_);
v___x_1967_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 1);
lean_ctor_set(v___x_1948_, 0, v___x_1967_);
v___x_1969_ = v___x_1948_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v_a_1944_);
lean_dec(v_json_1943_);
v___x_1972_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___boxed(lean_object* v_json_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_json_1974_, v_a_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(lean_object* v_json_1981_, lean_object* v_a_1982_){
_start:
{
if (lean_obj_tag(v_json_1981_) == 3)
{
lean_object* v_s_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1994_; 
v_s_1984_ = lean_ctor_get(v_json_1981_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_json_1981_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1986_ = v_json_1981_;
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_s_1984_);
lean_dec(v_json_1981_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 1);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_s_1984_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = l_Lean_Expr_lit___override(v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_a_1982_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref(v_a_1982_);
lean_dec(v_json_1981_);
v___x_1995_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1));
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___boxed(lean_object* v_json_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_json_1997_, v_a_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(lean_object* v_json_2006_, lean_object* v_a_2007_){
_start:
{
if (lean_obj_tag(v_json_2006_) == 5)
{
lean_object* v_kvPairs_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_kvPairs_2015_ = lean_ctor_get(v_json_2006_, 0);
v___x_2016_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2));
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2015_, v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 1)
{
lean_object* v_val_2018_; 
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v___x_2017_, 1);
if (lean_obj_tag(v_val_2018_) == 2)
{
lean_object* v_n_2019_; lean_object* v_mantissa_2020_; lean_object* v_exponent_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2066_; 
v_n_2019_ = lean_ctor_get(v_val_2018_, 0);
lean_inc_ref(v_n_2019_);
lean_dec_ref_known(v_val_2018_, 1);
v_mantissa_2020_ = lean_ctor_get(v_n_2019_, 0);
v_exponent_2021_ = lean_ctor_get(v_n_2019_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_n_2019_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2023_ = v_n_2019_;
v_isShared_2024_ = v_isSharedCheck_2066_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_exponent_2021_);
lean_inc(v_mantissa_2020_);
lean_dec(v_n_2019_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2066_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_natZero_2025_; lean_object* v_intZero_2026_; uint8_t v_isNeg_2027_; 
v_natZero_2025_ = lean_unsigned_to_nat(0u);
v_intZero_2026_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2027_ = lean_int_dec_lt(v_mantissa_2020_, v_intZero_2026_);
if (v_isNeg_2027_ == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_eq(v_exponent_2021_, v_natZero_2025_);
lean_dec(v_exponent_2021_);
if (v___x_2028_ == 0)
{
lean_del_object(v___x_2023_);
lean_dec(v_mantissa_2020_);
lean_dec_ref(v_a_2007_);
goto v___jp_2009_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3));
v___x_2030_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2015_, v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 1)
{
lean_object* v_val_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2065_; 
v_val_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_val_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
if (lean_obj_tag(v_val_2031_) == 5)
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2063_; 
v_isSharedCheck_2063_ = !lean_is_exclusive(v_val_2031_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_val_2031_, 0);
lean_dec(v_unused_2064_);
v___x_2036_ = v_val_2031_;
v_isShared_2037_ = v_isSharedCheck_2063_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v_val_2031_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2063_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_exprMap_2038_; lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_exprMap_2038_ = lean_ctor_get(v_a_2007_, 3);
v_a_2039_ = lean_nat_abs(v_mantissa_2020_);
lean_dec(v_mantissa_2020_);
v___x_2040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2038_, v_a_2039_);
if (lean_obj_tag(v___x_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_2039_);
lean_del_object(v___x_2036_);
lean_del_object(v___x_2033_);
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Lean_Expr_mdata___override(v___x_2045_, v_val_2041_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v_a_2007_);
lean_ctor_set(v___x_2023_, 0, v___x_2046_);
v___x_2048_ = v___x_2023_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_2007_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2048_);
v___x_2050_ = v___x_2043_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_dec(v___x_2040_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_a_2007_);
v___x_2054_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2055_ = l_Nat_reprFast(v_a_2039_);
v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
lean_dec_ref(v___x_2055_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 18);
lean_ctor_set(v___x_2036_, 0, v___x_2056_);
v___x_2058_ = v___x_2036_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2058_);
v___x_2060_ = v___x_2033_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_del_object(v___x_2033_);
lean_dec(v_val_2031_);
lean_del_object(v___x_2023_);
lean_dec(v_mantissa_2020_);
lean_dec_ref(v_a_2007_);
goto v___jp_2012_;
}
}
}
else
{
lean_dec(v___x_2030_);
lean_del_object(v___x_2023_);
lean_dec(v_mantissa_2020_);
lean_dec_ref(v_a_2007_);
goto v___jp_2012_;
}
}
}
else
{
lean_del_object(v___x_2023_);
lean_dec(v_exponent_2021_);
lean_dec(v_mantissa_2020_);
lean_dec_ref(v_a_2007_);
goto v___jp_2009_;
}
}
}
else
{
lean_dec(v_val_2018_);
lean_dec_ref(v_a_2007_);
goto v___jp_2009_;
}
}
else
{
lean_dec(v___x_2017_);
lean_dec_ref(v_a_2007_);
goto v___jp_2009_;
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec_ref(v_a_2007_);
v___x_2067_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
v___jp_2009_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
v___jp_2012_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___boxed(lean_object* v_json_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_json_2069_, v_a_2070_);
lean_dec(v_json_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = l_List_reverse___redArg(v_x_2077_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___y_2078_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
else
{
lean_object* v_head_2086_; 
v_head_2086_ = lean_ctor_get(v_x_2076_, 0);
lean_inc(v_head_2086_);
if (lean_obj_tag(v_head_2086_) == 2)
{
lean_object* v_n_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2118_; 
v_n_2087_ = lean_ctor_get(v_head_2086_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_head_2086_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2089_ = v_head_2086_;
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_n_2087_);
lean_dec(v_head_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_tail_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2116_; 
v_tail_2091_ = lean_ctor_get(v_x_2076_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v_x_2076_, 0);
lean_dec(v_unused_2117_);
v___x_2093_ = v_x_2076_;
v_isShared_2094_ = v_isSharedCheck_2116_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_tail_2091_);
lean_dec(v_x_2076_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2116_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_mantissa_2095_; lean_object* v_exponent_2096_; lean_object* v_natZero_2097_; lean_object* v_intZero_2098_; uint8_t v_isNeg_2099_; 
v_mantissa_2095_ = lean_ctor_get(v_n_2087_, 0);
lean_inc(v_mantissa_2095_);
v_exponent_2096_ = lean_ctor_get(v_n_2087_, 1);
lean_inc(v_exponent_2096_);
lean_dec_ref(v_n_2087_);
v_natZero_2097_ = lean_unsigned_to_nat(0u);
v_intZero_2098_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2099_ = lean_int_dec_lt(v_mantissa_2095_, v_intZero_2098_);
if (v_isNeg_2099_ == 0)
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_nat_dec_eq(v_exponent_2096_, v_natZero_2097_);
lean_dec(v_exponent_2096_);
if (v___x_2100_ == 0)
{
lean_dec(v_mantissa_2095_);
lean_del_object(v___x_2093_);
lean_dec(v_tail_2091_);
lean_del_object(v___x_2089_);
lean_dec_ref(v___y_2078_);
lean_dec(v_x_2077_);
goto v___jp_2080_;
}
else
{
lean_object* v_nameMap_2101_; lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_nameMap_2101_ = lean_ctor_get(v___y_2078_, 1);
v_a_2102_ = lean_nat_abs(v_mantissa_2095_);
lean_dec(v_mantissa_2095_);
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2103_) == 1)
{
lean_object* v_val_2104_; lean_object* v___x_2106_; 
lean_dec(v_a_2102_);
lean_del_object(v___x_2089_);
v_val_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_val_2104_);
lean_dec_ref_known(v___x_2103_, 1);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v_x_2077_);
lean_ctor_set(v___x_2093_, 0, v_val_2104_);
v___x_2106_ = v___x_2093_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_val_2104_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_x_2077_);
v___x_2106_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
v_x_2076_ = v_tail_2091_;
v_x_2077_ = v___x_2106_;
goto _start;
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v___x_2103_);
lean_del_object(v___x_2093_);
lean_dec(v_tail_2091_);
lean_dec_ref(v___y_2078_);
lean_dec(v_x_2077_);
v___x_2109_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2110_ = l_Nat_reprFast(v_a_2102_);
v___x_2111_ = lean_string_append(v___x_2109_, v___x_2110_);
lean_dec_ref(v___x_2110_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 18);
lean_ctor_set(v___x_2089_, 0, v___x_2111_);
v___x_2113_ = v___x_2089_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
}
}
else
{
lean_dec(v_exponent_2096_);
lean_dec(v_mantissa_2095_);
lean_del_object(v___x_2093_);
lean_dec(v_tail_2091_);
lean_del_object(v___x_2089_);
lean_dec_ref(v___y_2078_);
lean_dec(v_x_2077_);
goto v___jp_2080_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_2076_, 2);
lean_dec(v_head_2086_);
lean_dec_ref(v___y_2078_);
lean_dec(v_x_2077_);
goto v___jp_2080_;
}
}
v___jp_2080_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1));
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___boxed(lean_object* v_x_2119_, lean_object* v_x_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v_x_2119_, v_x_2120_, v___y_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(lean_object* v_idxs_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_array_to_list(v_idxs_2124_);
v___x_2128_ = lean_box(0);
v___x_2129_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v___x_2127_, v___x_2128_, v_a_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList___boxed(lean_object* v_idxs_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_idxs_2130_, v_a_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(lean_object* v_a_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
else
{
lean_object* v_key_2137_; lean_object* v_tail_2138_; uint8_t v___x_2139_; 
v_key_2137_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 2);
v___x_2139_ = lean_name_eq(v_key_2137_, v_a_2134_);
if (v___x_2139_ == 0)
{
v_x_2135_ = v_tail_2138_;
goto _start;
}
else
{
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
uint8_t v_res_2143_; lean_object* v_r_2144_; 
v_res_2143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec(v_a_2141_);
v_r_2144_ = lean_box(v_res_2143_);
return v_r_2144_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object* v_m_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_buckets_2147_; lean_object* v___x_2148_; uint64_t v___y_2150_; 
v_buckets_2147_ = lean_ctor_get(v_m_2145_, 1);
v___x_2148_ = lean_array_get_size(v_buckets_2147_);
if (lean_obj_tag(v_a_2146_) == 0)
{
uint64_t v___x_2164_; 
v___x_2164_ = 1723ULL;
v___y_2150_ = v___x_2164_;
goto v___jp_2149_;
}
else
{
uint64_t v_hash_2165_; 
v_hash_2165_ = lean_ctor_get_uint64(v_a_2146_, sizeof(void*)*2);
v___y_2150_ = v_hash_2165_;
goto v___jp_2149_;
}
v___jp_2149_:
{
uint64_t v___x_2151_; uint64_t v___x_2152_; uint64_t v_fold_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2151_ = 32ULL;
v___x_2152_ = lean_uint64_shift_right(v___y_2150_, v___x_2151_);
v_fold_2153_ = lean_uint64_xor(v___y_2150_, v___x_2152_);
v___x_2154_ = 16ULL;
v___x_2155_ = lean_uint64_shift_right(v_fold_2153_, v___x_2154_);
v___x_2156_ = lean_uint64_xor(v_fold_2153_, v___x_2155_);
v___x_2157_ = lean_uint64_to_usize(v___x_2156_);
v___x_2158_ = lean_usize_of_nat(v___x_2148_);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_sub(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_usize_land(v___x_2157_, v___x_2160_);
v___x_2162_ = lean_array_uget_borrowed(v_buckets_2147_, v___x_2161_);
v___x_2163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2146_, v___x_2162_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg___boxed(lean_object* v_m_2166_, lean_object* v_a_2167_){
_start:
{
uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_res_2168_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_m_2166_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
return v_x_2170_;
}
else
{
lean_object* v_key_2172_; lean_object* v_value_2173_; lean_object* v_tail_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2200_; 
v_key_2172_ = lean_ctor_get(v_x_2171_, 0);
v_value_2173_ = lean_ctor_get(v_x_2171_, 1);
v_tail_2174_ = lean_ctor_get(v_x_2171_, 2);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_x_2171_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2176_ = v_x_2171_;
v_isShared_2177_ = v_isSharedCheck_2200_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_tail_2174_);
lean_inc(v_value_2173_);
lean_inc(v_key_2172_);
lean_dec(v_x_2171_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2200_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; uint64_t v___y_2180_; 
v___x_2178_ = lean_array_get_size(v_x_2170_);
if (lean_obj_tag(v_key_2172_) == 0)
{
uint64_t v___x_2198_; 
v___x_2198_ = 1723ULL;
v___y_2180_ = v___x_2198_;
goto v___jp_2179_;
}
else
{
uint64_t v_hash_2199_; 
v_hash_2199_ = lean_ctor_get_uint64(v_key_2172_, sizeof(void*)*2);
v___y_2180_ = v_hash_2199_;
goto v___jp_2179_;
}
v___jp_2179_:
{
uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v_fold_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2181_ = 32ULL;
v___x_2182_ = lean_uint64_shift_right(v___y_2180_, v___x_2181_);
v_fold_2183_ = lean_uint64_xor(v___y_2180_, v___x_2182_);
v___x_2184_ = 16ULL;
v___x_2185_ = lean_uint64_shift_right(v_fold_2183_, v___x_2184_);
v___x_2186_ = lean_uint64_xor(v_fold_2183_, v___x_2185_);
v___x_2187_ = lean_uint64_to_usize(v___x_2186_);
v___x_2188_ = lean_usize_of_nat(v___x_2178_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_sub(v___x_2188_, v___x_2189_);
v___x_2191_ = lean_usize_land(v___x_2187_, v___x_2190_);
v___x_2192_ = lean_array_uget_borrowed(v_x_2170_, v___x_2191_);
lean_inc(v___x_2192_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 2, v___x_2192_);
v___x_2194_ = v___x_2176_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_key_2172_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_value_2173_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_array_uset(v_x_2170_, v___x_2191_, v___x_2194_);
v_x_2170_ = v___x_2195_;
v_x_2171_ = v_tail_2174_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2201_, lean_object* v_source_2202_, lean_object* v_target_2203_){
_start:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_array_get_size(v_source_2202_);
v___x_2205_ = lean_nat_dec_lt(v_i_2201_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_dec_ref(v_source_2202_);
lean_dec(v_i_2201_);
return v_target_2203_;
}
else
{
lean_object* v_es_2206_; lean_object* v___x_2207_; lean_object* v_source_2208_; lean_object* v_target_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_es_2206_ = lean_array_fget(v_source_2202_, v_i_2201_);
v___x_2207_ = lean_box(0);
v_source_2208_ = lean_array_fset(v_source_2202_, v_i_2201_, v___x_2207_);
v_target_2209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2203_, v_es_2206_);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_add(v_i_2201_, v___x_2210_);
lean_dec(v_i_2201_);
v_i_2201_ = v___x_2211_;
v_source_2202_ = v_source_2208_;
v_target_2203_ = v_target_2209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(lean_object* v_data_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_nbuckets_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2214_ = lean_array_get_size(v_data_2213_);
v___x_2215_ = lean_unsigned_to_nat(2u);
v_nbuckets_2216_ = lean_nat_mul(v___x_2214_, v___x_2215_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_mk_array(v_nbuckets_2216_, v___x_2218_);
v___x_2220_ = lean_array_propagate_mark(v_data_2213_, v___x_2219_);
v___x_2221_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v___x_2217_, v_data_2213_, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(lean_object* v_a_2222_, lean_object* v_b_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_dec(v_b_2223_);
lean_dec(v_a_2222_);
return v_x_2224_;
}
else
{
lean_object* v_key_2225_; lean_object* v_value_2226_; lean_object* v_tail_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2239_; 
v_key_2225_ = lean_ctor_get(v_x_2224_, 0);
v_value_2226_ = lean_ctor_get(v_x_2224_, 1);
v_tail_2227_ = lean_ctor_get(v_x_2224_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2229_ = v_x_2224_;
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_tail_2227_);
lean_inc(v_value_2226_);
lean_inc(v_key_2225_);
lean_dec(v_x_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_name_eq(v_key_2225_, v_a_2222_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2222_, v_b_2223_, v_tail_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 2, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_key_2225_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_value_2226_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v___x_2237_; 
lean_dec(v_value_2226_);
lean_dec(v_key_2225_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_b_2223_);
lean_ctor_set(v___x_2229_, 0, v_a_2222_);
v___x_2237_ = v___x_2229_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2222_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_b_2223_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_tail_2227_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object* v_m_2240_, lean_object* v_a_2241_, lean_object* v_b_2242_){
_start:
{
lean_object* v_size_2243_; lean_object* v_buckets_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2290_; 
v_size_2243_ = lean_ctor_get(v_m_2240_, 0);
v_buckets_2244_ = lean_ctor_get(v_m_2240_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_m_2240_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2246_ = v_m_2240_;
v_isShared_2247_ = v_isSharedCheck_2290_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_buckets_2244_);
lean_inc(v_size_2243_);
lean_dec(v_m_2240_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2290_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; uint64_t v___y_2250_; 
v___x_2248_ = lean_array_get_size(v_buckets_2244_);
if (lean_obj_tag(v_a_2241_) == 0)
{
uint64_t v___x_2288_; 
v___x_2288_ = 1723ULL;
v___y_2250_ = v___x_2288_;
goto v___jp_2249_;
}
else
{
uint64_t v_hash_2289_; 
v_hash_2289_ = lean_ctor_get_uint64(v_a_2241_, sizeof(void*)*2);
v___y_2250_ = v_hash_2289_;
goto v___jp_2249_;
}
v___jp_2249_:
{
uint64_t v___x_2251_; uint64_t v___x_2252_; uint64_t v_fold_2253_; uint64_t v___x_2254_; uint64_t v___x_2255_; uint64_t v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v_bkt_2262_; uint8_t v___x_2263_; 
v___x_2251_ = 32ULL;
v___x_2252_ = lean_uint64_shift_right(v___y_2250_, v___x_2251_);
v_fold_2253_ = lean_uint64_xor(v___y_2250_, v___x_2252_);
v___x_2254_ = 16ULL;
v___x_2255_ = lean_uint64_shift_right(v_fold_2253_, v___x_2254_);
v___x_2256_ = lean_uint64_xor(v_fold_2253_, v___x_2255_);
v___x_2257_ = lean_uint64_to_usize(v___x_2256_);
v___x_2258_ = lean_usize_of_nat(v___x_2248_);
v___x_2259_ = ((size_t)1ULL);
v___x_2260_ = lean_usize_sub(v___x_2258_, v___x_2259_);
v___x_2261_ = lean_usize_land(v___x_2257_, v___x_2260_);
v_bkt_2262_ = lean_array_uget_borrowed(v_buckets_2244_, v___x_2261_);
v___x_2263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2241_, v_bkt_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v_size_x27_2265_; lean_object* v___x_2266_; lean_object* v_buckets_x27_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2264_ = lean_unsigned_to_nat(1u);
v_size_x27_2265_ = lean_nat_add(v_size_2243_, v___x_2264_);
lean_dec(v_size_2243_);
lean_inc(v_bkt_2262_);
v___x_2266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2266_, 0, v_a_2241_);
lean_ctor_set(v___x_2266_, 1, v_b_2242_);
lean_ctor_set(v___x_2266_, 2, v_bkt_2262_);
v_buckets_x27_2267_ = lean_array_uset(v_buckets_2244_, v___x_2261_, v___x_2266_);
v___x_2268_ = lean_unsigned_to_nat(4u);
v___x_2269_ = lean_nat_mul(v_size_x27_2265_, v___x_2268_);
v___x_2270_ = lean_unsigned_to_nat(3u);
v___x_2271_ = lean_nat_div(v___x_2269_, v___x_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_array_get_size(v_buckets_x27_2267_);
v___x_2273_ = lean_nat_dec_le(v___x_2271_, v___x_2272_);
lean_dec(v___x_2271_);
if (v___x_2273_ == 0)
{
lean_object* v_val_2274_; lean_object* v___x_2276_; 
v_val_2274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_buckets_x27_2267_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v_val_2274_);
lean_ctor_set(v___x_2246_, 0, v_size_x27_2265_);
v___x_2276_ = v___x_2246_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_size_x27_2265_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_val_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
lean_object* v___x_2279_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v_buckets_x27_2267_);
lean_ctor_set(v___x_2246_, 0, v_size_x27_2265_);
v___x_2279_ = v___x_2246_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_size_x27_2265_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_buckets_x27_2267_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v_buckets_x27_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_inc(v_bkt_2262_);
v___x_2281_ = lean_box(0);
v_buckets_x27_2282_ = lean_array_uset(v_buckets_2244_, v___x_2261_, v___x_2281_);
v___x_2283_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2241_, v_b_2242_, v_bkt_2262_);
v___x_2284_ = lean_array_uset(v_buckets_x27_2282_, v___x_2261_, v___x_2283_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2284_);
v___x_2286_ = v___x_2246_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_size_2243_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(lean_object* v_data_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2296_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 1)
{
lean_object* v_val_2313_; 
v_val_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v___x_2312_, 1);
if (lean_obj_tag(v_val_2313_) == 2)
{
lean_object* v_n_2314_; lean_object* v_mantissa_2315_; lean_object* v_exponent_2316_; lean_object* v_natZero_2317_; lean_object* v_intZero_2318_; uint8_t v_isNeg_2319_; 
v_n_2314_ = lean_ctor_get(v_val_2313_, 0);
lean_inc_ref(v_n_2314_);
lean_dec_ref_known(v_val_2313_, 1);
v_mantissa_2315_ = lean_ctor_get(v_n_2314_, 0);
lean_inc(v_mantissa_2315_);
v_exponent_2316_ = lean_ctor_get(v_n_2314_, 1);
lean_inc(v_exponent_2316_);
lean_dec_ref(v_n_2314_);
v_natZero_2317_ = lean_unsigned_to_nat(0u);
v_intZero_2318_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2319_ = lean_int_dec_lt(v_mantissa_2315_, v_intZero_2318_);
if (v_isNeg_2319_ == 0)
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_nat_dec_eq(v_exponent_2316_, v_natZero_2317_);
lean_dec(v_exponent_2316_);
if (v___x_2320_ == 0)
{
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2299_;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2296_, v___x_2321_);
if (lean_obj_tag(v___x_2322_) == 1)
{
lean_object* v_val_2323_; 
v_val_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_val_2323_);
lean_dec_ref_known(v___x_2322_, 1);
if (lean_obj_tag(v_val_2323_) == 4)
{
lean_object* v_elems_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_elems_2324_ = lean_ctor_get(v_val_2323_, 0);
lean_inc_ref(v_elems_2324_);
lean_dec_ref_known(v_val_2323_, 1);
v___x_2325_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2296_, v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 1)
{
lean_object* v_val_2327_; 
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2326_, 1);
if (lean_obj_tag(v_val_2327_) == 2)
{
lean_object* v_n_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2435_; 
v_n_2328_ = lean_ctor_get(v_val_2327_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_val_2327_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2330_ = v_val_2327_;
v_isShared_2331_ = v_isSharedCheck_2435_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_n_2328_);
lean_dec(v_val_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2435_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_mantissa_2332_; lean_object* v_exponent_2333_; uint8_t v_isNeg_2334_; 
v_mantissa_2332_ = lean_ctor_get(v_n_2328_, 0);
lean_inc(v_mantissa_2332_);
v_exponent_2333_ = lean_ctor_get(v_n_2328_, 1);
lean_inc(v_exponent_2333_);
lean_dec_ref(v_n_2328_);
v_isNeg_2334_ = lean_int_dec_lt(v_mantissa_2332_, v_intZero_2318_);
if (v_isNeg_2334_ == 0)
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_nat_dec_eq(v_exponent_2333_, v_natZero_2317_);
lean_dec(v_exponent_2333_);
if (v___x_2335_ == 0)
{
lean_dec(v_mantissa_2332_);
lean_del_object(v___x_2330_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2305_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_2337_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2296_, v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 1)
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2434_; 
v_val_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2434_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2434_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
if (lean_obj_tag(v_val_2338_) == 1)
{
uint8_t v_b_2342_; lean_object* v_nameMap_2343_; lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_b_2342_ = lean_ctor_get_uint8(v_val_2338_, 0);
lean_dec_ref_known(v_val_2338_, 0);
v_nameMap_2343_ = lean_ctor_get(v_a_2297_, 1);
v_a_2344_ = lean_nat_abs(v_mantissa_2315_);
lean_dec(v_mantissa_2315_);
v___x_2345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2345_) == 1)
{
lean_object* v_val_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_a_2344_);
lean_del_object(v___x_2340_);
lean_del_object(v___x_2330_);
v_val_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2424_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_val_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2424_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_nat_abs(v_mantissa_2332_);
lean_dec(v_mantissa_2332_);
v___x_2351_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2324_, v_a_2297_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2415_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2415_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2415_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_snd_2356_; lean_object* v_fst_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2414_; 
v_snd_2356_ = lean_ctor_get(v_a_2352_, 1);
v_fst_2357_ = lean_ctor_get(v_a_2352_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_a_2352_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2359_ = v_a_2352_;
v_isShared_2360_ = v_isSharedCheck_2414_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snd_2356_);
lean_inc(v_fst_2357_);
lean_dec(v_a_2352_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2414_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_stream_2361_; lean_object* v_nameMap_2362_; lean_object* v_levelMap_2363_; lean_object* v_exprMap_2364_; lean_object* v_recursorRuleMap_2365_; lean_object* v_constMap_2366_; lean_object* v_constOrder_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2413_; 
v_stream_2361_ = lean_ctor_get(v_snd_2356_, 0);
v_nameMap_2362_ = lean_ctor_get(v_snd_2356_, 1);
v_levelMap_2363_ = lean_ctor_get(v_snd_2356_, 2);
v_exprMap_2364_ = lean_ctor_get(v_snd_2356_, 3);
v_recursorRuleMap_2365_ = lean_ctor_get(v_snd_2356_, 4);
v_constMap_2366_ = lean_ctor_get(v_snd_2356_, 5);
v_constOrder_2367_ = lean_ctor_get(v_snd_2356_, 6);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_snd_2356_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2369_ = v_snd_2356_;
v_isShared_2370_ = v_isSharedCheck_2413_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_constOrder_2367_);
lean_inc(v_constMap_2366_);
lean_inc(v_recursorRuleMap_2365_);
lean_inc(v_exprMap_2364_);
lean_inc(v_levelMap_2363_);
lean_inc(v_nameMap_2362_);
lean_inc(v_stream_2361_);
lean_dec(v_snd_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2413_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2364_, v_a_2350_);
if (lean_obj_tag(v___x_2371_) == 1)
{
lean_object* v_val_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2350_);
lean_del_object(v___x_2348_);
v_val_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2403_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_val_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2403_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
lean_inc(v_val_2346_);
v___x_2376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2376_, 0, v_val_2346_);
lean_ctor_set(v___x_2376_, 1, v_fst_2357_);
lean_ctor_set(v___x_2376_, 2, v_val_2372_);
v___x_2377_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2366_, v_val_2346_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set_uint8(v___x_2378_, sizeof(void*)*1, v_b_2342_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2378_);
v___x_2380_ = v___x_2374_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2381_ = lean_box(0);
lean_inc(v_val_2346_);
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2366_, v_val_2346_, v___x_2380_);
v___x_2383_ = lean_array_push(v_constOrder_2367_, v_val_2346_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 6, v___x_2383_);
lean_ctor_set(v___x_2369_, 5, v___x_2382_);
v___x_2385_ = v___x_2369_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_stream_2361_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_nameMap_2362_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_levelMap_2363_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_exprMap_2364_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_recursorRuleMap_2365_);
lean_ctor_set(v_reuseFailAlloc_2392_, 5, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 6, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2385_);
lean_ctor_set(v___x_2359_, 0, v___x_2381_);
v___x_2387_ = v___x_2359_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2387_);
v___x_2389_ = v___x_2354_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_dec_ref_known(v___x_2376_, 3);
lean_del_object(v___x_2369_);
lean_dec_ref(v_constOrder_2367_);
lean_dec_ref(v_constMap_2366_);
lean_dec_ref(v_recursorRuleMap_2365_);
lean_dec_ref(v_exprMap_2364_);
lean_dec_ref(v_levelMap_2363_);
lean_dec_ref(v_nameMap_2362_);
lean_dec_ref(v_stream_2361_);
lean_del_object(v___x_2359_);
v___x_2394_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2346_, v___x_2377_);
v___x_2396_ = lean_string_append(v___x_2394_, v___x_2395_);
lean_dec_ref(v___x_2395_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 18);
lean_ctor_set(v___x_2374_, 0, v___x_2396_);
v___x_2398_ = v___x_2374_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 1);
lean_ctor_set(v___x_2354_, 0, v___x_2398_);
v___x_2400_ = v___x_2354_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_dec(v___x_2371_);
lean_del_object(v___x_2369_);
lean_dec_ref(v_constOrder_2367_);
lean_dec_ref(v_constMap_2366_);
lean_dec_ref(v_recursorRuleMap_2365_);
lean_dec_ref(v_exprMap_2364_);
lean_dec_ref(v_levelMap_2363_);
lean_dec_ref(v_nameMap_2362_);
lean_dec_ref(v_stream_2361_);
lean_del_object(v___x_2359_);
lean_dec(v_fst_2357_);
lean_dec(v_val_2346_);
v___x_2404_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2405_ = l_Nat_reprFast(v_a_2350_);
v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
lean_dec_ref(v___x_2405_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 18);
lean_ctor_set(v___x_2348_, 0, v___x_2406_);
v___x_2408_ = v___x_2348_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 1);
lean_ctor_set(v___x_2354_, 0, v___x_2408_);
v___x_2410_ = v___x_2354_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_a_2350_);
lean_del_object(v___x_2348_);
lean_dec(v_val_2346_);
v_a_2416_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2351_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2351_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_dec(v___x_2345_);
lean_dec(v_mantissa_2332_);
lean_dec_ref(v_elems_2324_);
lean_dec_ref(v_a_2297_);
v___x_2425_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2426_ = l_Nat_reprFast(v_a_2344_);
v___x_2427_ = lean_string_append(v___x_2425_, v___x_2426_);
lean_dec_ref(v___x_2426_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 18);
lean_ctor_set(v___x_2340_, 0, v___x_2427_);
v___x_2429_ = v___x_2340_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2431_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 1);
lean_ctor_set(v___x_2330_, 0, v___x_2429_);
v___x_2431_ = v___x_2330_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
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
else
{
lean_del_object(v___x_2340_);
lean_dec(v_val_2338_);
lean_dec(v_mantissa_2332_);
lean_del_object(v___x_2330_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2308_;
}
}
}
else
{
lean_dec(v___x_2337_);
lean_dec(v_mantissa_2332_);
lean_del_object(v___x_2330_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2308_;
}
}
}
else
{
lean_dec(v_exponent_2333_);
lean_dec(v_mantissa_2332_);
lean_del_object(v___x_2330_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2305_;
}
}
}
else
{
lean_dec(v_val_2327_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2305_;
}
}
else
{
lean_dec(v___x_2326_);
lean_dec_ref(v_elems_2324_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2305_;
}
}
else
{
lean_dec(v_val_2323_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2302_;
}
}
else
{
lean_dec(v___x_2322_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2302_;
}
}
}
else
{
lean_dec(v_exponent_2316_);
lean_dec(v_mantissa_2315_);
lean_dec_ref(v_a_2297_);
goto v___jp_2299_;
}
}
else
{
lean_dec(v_val_2313_);
lean_dec_ref(v_a_2297_);
goto v___jp_2299_;
}
}
else
{
lean_dec(v___x_2312_);
lean_dec_ref(v_a_2297_);
goto v___jp_2299_;
}
v___jp_2299_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
v___jp_2302_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
v___jp_2305_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
v___jp_2308_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___boxed(lean_object* v_data_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_data_2436_, v_a_2437_);
lean_dec(v_data_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_object* v_00_u03b2_2440_, lean_object* v_m_2441_, lean_object* v_a_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2441_, v_a_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___boxed(lean_object* v_00_u03b2_2444_, lean_object* v_m_2445_, lean_object* v_a_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(v_00_u03b2_2444_, v_m_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_m_2445_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1(lean_object* v_00_u03b2_2449_, lean_object* v_m_2450_, lean_object* v_a_2451_, lean_object* v_b_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_m_2450_, v_a_2451_, v_b_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_object* v_00_u03b2_2454_, lean_object* v_a_2455_, lean_object* v_x_2456_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2455_, v_x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2458_, lean_object* v_a_2459_, lean_object* v_x_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(v_00_u03b2_2458_, v_a_2459_, v_x_2460_);
lean_dec(v_x_2460_);
lean_dec(v_a_2459_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2(lean_object* v_00_u03b2_2463_, lean_object* v_data_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_data_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3(lean_object* v_00_u03b2_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_, lean_object* v_x_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2467_, v_b_2468_, v_x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2471_, lean_object* v_i_2472_, lean_object* v_source_2473_, lean_object* v_target_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v_i_2472_, v_source_2473_, v_target_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2477_, v_x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(lean_object* v_data_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2520_);
if (lean_obj_tag(v___x_2521_) == 1)
{
lean_object* v_val_2522_; 
v_val_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v___x_2521_, 1);
if (lean_obj_tag(v_val_2522_) == 2)
{
lean_object* v_n_2523_; lean_object* v_mantissa_2524_; lean_object* v_exponent_2525_; lean_object* v_natZero_2526_; lean_object* v_intZero_2527_; uint8_t v_isNeg_2528_; 
v_n_2523_ = lean_ctor_get(v_val_2522_, 0);
lean_inc_ref(v_n_2523_);
lean_dec_ref_known(v_val_2522_, 1);
v_mantissa_2524_ = lean_ctor_get(v_n_2523_, 0);
lean_inc(v_mantissa_2524_);
v_exponent_2525_ = lean_ctor_get(v_n_2523_, 1);
lean_inc(v_exponent_2525_);
lean_dec_ref(v_n_2523_);
v_natZero_2526_ = lean_unsigned_to_nat(0u);
v_intZero_2527_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2528_ = lean_int_dec_lt(v_mantissa_2524_, v_intZero_2527_);
if (v_isNeg_2528_ == 0)
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_nat_dec_eq(v_exponent_2525_, v_natZero_2526_);
lean_dec(v_exponent_2525_);
if (v___x_2529_ == 0)
{
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2496_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2530_);
if (lean_obj_tag(v___x_2531_) == 1)
{
lean_object* v_val_2532_; 
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2531_, 1);
if (lean_obj_tag(v_val_2532_) == 4)
{
lean_object* v_elems_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_elems_2533_ = lean_ctor_get(v_val_2532_, 0);
lean_inc_ref(v_elems_2533_);
lean_dec_ref_known(v_val_2532_, 1);
v___x_2534_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 1)
{
lean_object* v_val_2536_; 
v_val_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v___x_2535_, 1);
if (lean_obj_tag(v_val_2536_) == 2)
{
lean_object* v_n_2537_; lean_object* v_mantissa_2538_; lean_object* v_exponent_2539_; uint8_t v_isNeg_2540_; 
v_n_2537_ = lean_ctor_get(v_val_2536_, 0);
lean_inc_ref(v_n_2537_);
lean_dec_ref_known(v_val_2536_, 1);
v_mantissa_2538_ = lean_ctor_get(v_n_2537_, 0);
lean_inc(v_mantissa_2538_);
v_exponent_2539_ = lean_ctor_get(v_n_2537_, 1);
lean_inc(v_exponent_2539_);
lean_dec_ref(v_n_2537_);
v_isNeg_2540_ = lean_int_dec_lt(v_mantissa_2538_, v_intZero_2527_);
if (v_isNeg_2540_ == 0)
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_nat_dec_eq(v_exponent_2539_, v_natZero_2526_);
lean_dec(v_exponent_2539_);
if (v___x_2541_ == 0)
{
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2502_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2542_);
if (lean_obj_tag(v___x_2543_) == 1)
{
lean_object* v_val_2544_; 
v_val_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref_known(v___x_2543_, 1);
if (lean_obj_tag(v_val_2544_) == 2)
{
lean_object* v_n_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2743_; 
v_n_2545_ = lean_ctor_get(v_val_2544_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_val_2544_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2547_ = v_val_2544_;
v_isShared_2548_ = v_isSharedCheck_2743_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_n_2545_);
lean_dec(v_val_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2743_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_mantissa_2549_; lean_object* v_exponent_2550_; uint8_t v_isNeg_2551_; 
v_mantissa_2549_ = lean_ctor_get(v_n_2545_, 0);
lean_inc(v_mantissa_2549_);
v_exponent_2550_ = lean_ctor_get(v_n_2545_, 1);
lean_inc(v_exponent_2550_);
lean_dec_ref(v_n_2545_);
v_isNeg_2551_ = lean_int_dec_lt(v_mantissa_2549_, v_intZero_2527_);
if (v_isNeg_2551_ == 0)
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_nat_dec_eq(v_exponent_2550_, v_natZero_2526_);
lean_dec(v_exponent_2550_);
if (v___x_2552_ == 0)
{
lean_dec(v_mantissa_2549_);
lean_del_object(v___x_2547_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2505_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2));
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2553_);
if (lean_obj_tag(v___x_2554_) == 1)
{
lean_object* v_val_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_del_object(v___x_2547_);
v_val_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3));
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 1)
{
lean_object* v_val_2558_; 
v_val_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v___x_2557_, 1);
if (lean_obj_tag(v_val_2558_) == 3)
{
lean_object* v_s_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_s_2559_ = lean_ctor_get(v_val_2558_, 0);
lean_inc_ref(v_s_2559_);
lean_dec_ref_known(v_val_2558_, 1);
v___x_2560_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2493_, v___x_2560_);
if (lean_obj_tag(v___x_2561_) == 1)
{
lean_object* v_val_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2738_; 
v_val_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2738_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_val_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2738_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (lean_obj_tag(v_val_2562_) == 4)
{
lean_object* v_elems_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2737_; 
v_elems_2566_ = lean_ctor_get(v_val_2562_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_val_2562_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2568_ = v_val_2562_;
v_isShared_2569_ = v_isSharedCheck_2737_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_elems_2566_);
lean_dec(v_val_2562_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2737_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_nameMap_2570_; lean_object* v_a_2571_; lean_object* v___x_2572_; 
v_nameMap_2570_ = lean_ctor_get(v_a_2494_, 1);
v_a_2571_ = lean_nat_abs(v_mantissa_2524_);
lean_dec(v_mantissa_2524_);
v___x_2572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2570_, v_a_2571_);
if (lean_obj_tag(v___x_2572_) == 1)
{
lean_object* v_val_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2571_);
lean_del_object(v___x_2568_);
lean_del_object(v___x_2564_);
v_val_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2727_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_val_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2727_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_a_2577_; lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2577_ = lean_nat_abs(v_mantissa_2538_);
lean_dec(v_mantissa_2538_);
v_a_2578_ = lean_nat_abs(v_mantissa_2549_);
lean_dec(v_mantissa_2549_);
v___x_2579_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2533_, v_a_2494_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2718_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2718_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2718_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_snd_2584_; lean_object* v_fst_2585_; lean_object* v_exprMap_2586_; lean_object* v___x_2587_; 
v_snd_2584_ = lean_ctor_get(v_a_2580_, 1);
lean_inc(v_snd_2584_);
v_fst_2585_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_fst_2585_);
lean_dec(v_a_2580_);
v_exprMap_2586_ = lean_ctor_get(v_snd_2584_, 3);
v___x_2587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2586_, v_a_2577_);
if (lean_obj_tag(v___x_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2577_);
lean_del_object(v___x_2575_);
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2708_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_val_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2708_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2586_, v_a_2578_);
if (lean_obj_tag(v___x_2592_) == 1)
{
lean_object* v_val_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2578_);
v_val_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2698_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_val_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2698_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___y_2598_; uint8_t v_safety_2599_; lean_object* v___y_2600_; lean_object* v_hints_2660_; lean_object* v___y_2661_; 
switch(lean_obj_tag(v_val_2555_))
{
case 3:
{
lean_object* v_s_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_s_2679_ = lean_ctor_get(v_val_2555_, 0);
lean_inc_ref(v_s_2679_);
lean_dec_ref_known(v_val_2555_, 1);
v___x_2680_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_2681_ = lean_string_dec_eq(v_s_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10));
v___x_2683_ = lean_string_dec_eq(v_s_2679_, v___x_2682_);
lean_dec_ref(v_s_2679_);
if (v___x_2683_ == 0)
{
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
goto v___jp_2517_;
}
else
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_box(1);
v_hints_2660_ = v___x_2684_;
v___y_2661_ = v_snd_2584_;
goto v___jp_2659_;
}
}
else
{
lean_object* v___x_2685_; 
lean_dec_ref(v_s_2679_);
v___x_2685_ = lean_box(0);
v_hints_2660_ = v___x_2685_;
v___y_2661_ = v_snd_2584_;
goto v___jp_2659_;
}
}
case 5:
{
lean_object* v_kvPairs_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_kvPairs_2686_ = lean_ctor_get(v_val_2555_, 0);
lean_inc(v_kvPairs_2686_);
lean_dec_ref_known(v_val_2555_, 1);
v___x_2687_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11));
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2686_, v___x_2687_);
lean_dec(v_kvPairs_2686_);
if (lean_obj_tag(v___x_2688_) == 1)
{
lean_object* v_val_2689_; 
v_val_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v___x_2688_, 1);
if (lean_obj_tag(v_val_2689_) == 2)
{
lean_object* v_n_2690_; lean_object* v_mantissa_2691_; lean_object* v_exponent_2692_; uint8_t v_isNeg_2693_; 
v_n_2690_ = lean_ctor_get(v_val_2689_, 0);
lean_inc_ref(v_n_2690_);
lean_dec_ref_known(v_val_2689_, 1);
v_mantissa_2691_ = lean_ctor_get(v_n_2690_, 0);
lean_inc(v_mantissa_2691_);
v_exponent_2692_ = lean_ctor_get(v_n_2690_, 1);
lean_inc(v_exponent_2692_);
lean_dec_ref(v_n_2690_);
v_isNeg_2693_ = lean_int_dec_lt(v_mantissa_2691_, v_intZero_2527_);
if (v_isNeg_2693_ == 0)
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_nat_dec_eq(v_exponent_2692_, v_natZero_2526_);
lean_dec(v_exponent_2692_);
if (v___x_2694_ == 0)
{
lean_dec(v_mantissa_2691_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
goto v___jp_2514_;
}
else
{
lean_object* v_a_2695_; uint32_t v___x_2696_; lean_object* v___x_2697_; 
v_a_2695_ = lean_nat_abs(v_mantissa_2691_);
lean_dec(v_mantissa_2691_);
v___x_2696_ = lean_uint32_of_nat(v_a_2695_);
lean_dec(v_a_2695_);
v___x_2697_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_2697_, 0, v___x_2696_);
v_hints_2660_ = v___x_2697_;
v___y_2661_ = v_snd_2584_;
goto v___jp_2659_;
}
}
else
{
lean_dec(v_exponent_2692_);
lean_dec(v_mantissa_2691_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
goto v___jp_2514_;
}
}
else
{
lean_dec(v_val_2689_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
goto v___jp_2514_;
}
}
else
{
lean_dec(v___x_2688_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
goto v___jp_2514_;
}
}
default: 
{
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
goto v___jp_2517_;
}
}
v___jp_2597_:
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2566_, v___y_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2650_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2650_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2650_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_snd_2606_; lean_object* v_fst_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2649_; 
v_snd_2606_ = lean_ctor_get(v_a_2602_, 1);
v_fst_2607_ = lean_ctor_get(v_a_2602_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2609_ = v_a_2602_;
v_isShared_2610_ = v_isSharedCheck_2649_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_snd_2606_);
lean_inc(v_fst_2607_);
lean_dec(v_a_2602_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2649_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_stream_2611_; lean_object* v_nameMap_2612_; lean_object* v_levelMap_2613_; lean_object* v_exprMap_2614_; lean_object* v_recursorRuleMap_2615_; lean_object* v_constMap_2616_; lean_object* v_constOrder_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2648_; 
v_stream_2611_ = lean_ctor_get(v_snd_2606_, 0);
v_nameMap_2612_ = lean_ctor_get(v_snd_2606_, 1);
v_levelMap_2613_ = lean_ctor_get(v_snd_2606_, 2);
v_exprMap_2614_ = lean_ctor_get(v_snd_2606_, 3);
v_recursorRuleMap_2615_ = lean_ctor_get(v_snd_2606_, 4);
v_constMap_2616_ = lean_ctor_get(v_snd_2606_, 5);
v_constOrder_2617_ = lean_ctor_get(v_snd_2606_, 6);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_snd_2606_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2619_ = v_snd_2606_;
v_isShared_2620_ = v_isSharedCheck_2648_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_constOrder_2617_);
lean_inc(v_constMap_2616_);
lean_inc(v_recursorRuleMap_2615_);
lean_inc(v_exprMap_2614_);
lean_inc(v_levelMap_2613_);
lean_inc(v_nameMap_2612_);
lean_inc(v_stream_2611_);
lean_dec(v_snd_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2648_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
uint8_t v___x_2621_; 
v___x_2621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2616_, v_val_2573_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_inc(v_val_2573_);
v___x_2622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2622_, 0, v_val_2573_);
lean_ctor_set(v___x_2622_, 1, v_fst_2585_);
lean_ctor_set(v___x_2622_, 2, v_val_2588_);
v___x_2623_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_val_2593_);
lean_ctor_set(v___x_2623_, 2, v___y_2598_);
lean_ctor_set(v___x_2623_, 3, v_fst_2607_);
lean_ctor_set_uint8(v___x_2623_, sizeof(void*)*4, v_safety_2599_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2623_);
v___x_2625_ = v___x_2595_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2626_ = lean_box(0);
lean_inc(v_val_2573_);
v___x_2627_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2616_, v_val_2573_, v___x_2625_);
v___x_2628_ = lean_array_push(v_constOrder_2617_, v_val_2573_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 6, v___x_2628_);
lean_ctor_set(v___x_2619_, 5, v___x_2627_);
v___x_2630_ = v___x_2619_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_stream_2611_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_nameMap_2612_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_levelMap_2613_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_exprMap_2614_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_recursorRuleMap_2615_);
lean_ctor_set(v_reuseFailAlloc_2637_, 5, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2637_, 6, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 1, v___x_2630_);
lean_ctor_set(v___x_2609_, 0, v___x_2626_);
v___x_2632_ = v___x_2609_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2632_);
v___x_2634_ = v___x_2604_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_del_object(v___x_2619_);
lean_dec_ref(v_constOrder_2617_);
lean_dec_ref(v_constMap_2616_);
lean_dec_ref(v_recursorRuleMap_2615_);
lean_dec_ref(v_exprMap_2614_);
lean_dec_ref(v_levelMap_2613_);
lean_dec_ref(v_nameMap_2612_);
lean_dec_ref(v_stream_2611_);
lean_del_object(v___x_2609_);
lean_dec(v_fst_2607_);
lean_dec(v___y_2598_);
lean_dec(v_val_2593_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
v___x_2639_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2573_, v___x_2621_);
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
lean_dec_ref(v___x_2640_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 18);
lean_ctor_set(v___x_2595_, 0, v___x_2641_);
v___x_2643_ = v___x_2595_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 1);
lean_ctor_set(v___x_2604_, 0, v___x_2643_);
v___x_2645_ = v___x_2604_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v___y_2598_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_val_2573_);
v_a_2651_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2601_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2601_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5));
v___x_2663_ = lean_string_dec_eq(v_s_2559_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6));
v___x_2665_ = lean_string_dec_eq(v_s_2559_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7));
v___x_2667_ = lean_string_dec_eq(v_s_2559_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_dec_ref(v___y_2661_);
lean_dec(v_hints_2660_);
lean_del_object(v___x_2595_);
lean_dec(v_val_2593_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
v___x_2668_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8));
v___x_2669_ = lean_string_append(v___x_2668_, v_s_2559_);
lean_dec_ref(v_s_2559_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 18);
lean_ctor_set(v___x_2590_, 0, v___x_2669_);
v___x_2671_ = v___x_2590_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2671_);
v___x_2673_ = v___x_2582_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
uint8_t v___x_2676_; 
lean_del_object(v___x_2590_);
lean_del_object(v___x_2582_);
lean_dec_ref(v_s_2559_);
v___x_2676_ = 2;
v___y_2598_ = v_hints_2660_;
v_safety_2599_ = v___x_2676_;
v___y_2600_ = v___y_2661_;
goto v___jp_2597_;
}
}
else
{
uint8_t v___x_2677_; 
lean_del_object(v___x_2590_);
lean_del_object(v___x_2582_);
lean_dec_ref(v_s_2559_);
v___x_2677_ = 1;
v___y_2598_ = v_hints_2660_;
v_safety_2599_ = v___x_2677_;
v___y_2600_ = v___y_2661_;
goto v___jp_2597_;
}
}
else
{
uint8_t v___x_2678_; 
lean_del_object(v___x_2590_);
lean_del_object(v___x_2582_);
lean_dec_ref(v_s_2559_);
v___x_2678_ = 0;
v___y_2598_ = v_hints_2660_;
v_safety_2599_ = v___x_2678_;
v___y_2600_ = v___y_2661_;
goto v___jp_2597_;
}
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec(v___x_2592_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
v___x_2699_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2700_ = l_Nat_reprFast(v_a_2578_);
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
lean_dec_ref(v___x_2700_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 18);
lean_ctor_set(v___x_2590_, 0, v___x_2701_);
v___x_2703_ = v___x_2590_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2703_);
v___x_2705_ = v___x_2582_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_dec(v___x_2587_);
lean_dec(v_fst_2585_);
lean_dec(v_snd_2584_);
lean_dec(v_a_2578_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
v___x_2709_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2710_ = l_Nat_reprFast(v_a_2577_);
v___x_2711_ = lean_string_append(v___x_2709_, v___x_2710_);
lean_dec_ref(v___x_2710_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 18);
lean_ctor_set(v___x_2575_, 0, v___x_2711_);
v___x_2713_ = v___x_2575_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2715_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2713_);
v___x_2715_ = v___x_2582_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2578_);
lean_dec(v_a_2577_);
lean_del_object(v___x_2575_);
lean_dec(v_val_2573_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
v_a_2719_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2579_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2579_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
lean_dec(v___x_2572_);
lean_dec_ref(v_elems_2566_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec_ref(v_a_2494_);
v___x_2728_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2729_ = l_Nat_reprFast(v_a_2571_);
v___x_2730_ = lean_string_append(v___x_2728_, v___x_2729_);
lean_dec_ref(v___x_2729_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 18);
lean_ctor_set(v___x_2568_, 0, v___x_2730_);
v___x_2732_ = v___x_2568_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2732_);
v___x_2734_ = v___x_2564_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
else
{
lean_del_object(v___x_2564_);
lean_dec(v_val_2562_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2511_;
}
}
}
else
{
lean_dec(v___x_2561_);
lean_dec_ref(v_s_2559_);
lean_dec(v_val_2555_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2511_;
}
}
else
{
lean_dec(v_val_2558_);
lean_dec(v_val_2555_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2508_;
}
}
else
{
lean_dec(v___x_2557_);
lean_dec(v_val_2555_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2508_;
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec(v___x_2554_);
lean_dec(v_mantissa_2549_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
v___x_2739_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 1);
lean_ctor_set(v___x_2547_, 0, v___x_2739_);
v___x_2741_ = v___x_2547_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_dec(v_exponent_2550_);
lean_dec(v_mantissa_2549_);
lean_del_object(v___x_2547_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2505_;
}
}
}
else
{
lean_dec(v_val_2544_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2505_;
}
}
else
{
lean_dec(v___x_2543_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2505_;
}
}
}
else
{
lean_dec(v_exponent_2539_);
lean_dec(v_mantissa_2538_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2502_;
}
}
else
{
lean_dec(v_val_2536_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2502_;
}
}
else
{
lean_dec(v___x_2535_);
lean_dec_ref(v_elems_2533_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2502_;
}
}
else
{
lean_dec(v_val_2532_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2499_;
}
}
else
{
lean_dec(v___x_2531_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2499_;
}
}
}
else
{
lean_dec(v_exponent_2525_);
lean_dec(v_mantissa_2524_);
lean_dec_ref(v_a_2494_);
goto v___jp_2496_;
}
}
else
{
lean_dec(v_val_2522_);
lean_dec_ref(v_a_2494_);
goto v___jp_2496_;
}
}
else
{
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2494_);
goto v___jp_2496_;
}
v___jp_2496_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
v___jp_2502_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
v___jp_2505_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
v___jp_2508_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
v___jp_2511_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
v___jp_2514_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
v___jp_2517_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___boxed(lean_object* v_data_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_data_2744_, v_a_2745_);
lean_dec(v_data_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(lean_object* v_data_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2751_, v___x_2769_);
if (lean_obj_tag(v___x_2770_) == 1)
{
lean_object* v_val_2771_; 
v_val_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v___x_2770_, 1);
if (lean_obj_tag(v_val_2771_) == 2)
{
lean_object* v_n_2772_; lean_object* v_mantissa_2773_; lean_object* v_exponent_2774_; lean_object* v_natZero_2775_; lean_object* v_intZero_2776_; uint8_t v_isNeg_2777_; 
v_n_2772_ = lean_ctor_get(v_val_2771_, 0);
lean_inc_ref(v_n_2772_);
lean_dec_ref_known(v_val_2771_, 1);
v_mantissa_2773_ = lean_ctor_get(v_n_2772_, 0);
lean_inc(v_mantissa_2773_);
v_exponent_2774_ = lean_ctor_get(v_n_2772_, 1);
lean_inc(v_exponent_2774_);
lean_dec_ref(v_n_2772_);
v_natZero_2775_ = lean_unsigned_to_nat(0u);
v_intZero_2776_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2777_ = lean_int_dec_lt(v_mantissa_2773_, v_intZero_2776_);
if (v_isNeg_2777_ == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = lean_nat_dec_eq(v_exponent_2774_, v_natZero_2775_);
lean_dec(v_exponent_2774_);
if (v___x_2778_ == 0)
{
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2754_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2751_, v___x_2779_);
if (lean_obj_tag(v___x_2780_) == 1)
{
lean_object* v_val_2781_; 
v_val_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___x_2780_, 1);
if (lean_obj_tag(v_val_2781_) == 4)
{
lean_object* v_elems_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_elems_2782_ = lean_ctor_get(v_val_2781_, 0);
lean_inc_ref(v_elems_2782_);
lean_dec_ref_known(v_val_2781_, 1);
v___x_2783_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2751_, v___x_2783_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v_val_2785_; 
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
if (lean_obj_tag(v_val_2785_) == 2)
{
lean_object* v_n_2786_; lean_object* v_mantissa_2787_; lean_object* v_exponent_2788_; uint8_t v_isNeg_2789_; 
v_n_2786_ = lean_ctor_get(v_val_2785_, 0);
lean_inc_ref(v_n_2786_);
lean_dec_ref_known(v_val_2785_, 1);
v_mantissa_2787_ = lean_ctor_get(v_n_2786_, 0);
lean_inc(v_mantissa_2787_);
v_exponent_2788_ = lean_ctor_get(v_n_2786_, 1);
lean_inc(v_exponent_2788_);
lean_dec_ref(v_n_2786_);
v_isNeg_2789_ = lean_int_dec_lt(v_mantissa_2787_, v_intZero_2776_);
if (v_isNeg_2789_ == 0)
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_nat_dec_eq(v_exponent_2788_, v_natZero_2775_);
lean_dec(v_exponent_2788_);
if (v___x_2790_ == 0)
{
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2760_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2751_, v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 1)
{
lean_object* v_val_2793_; 
v_val_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_val_2793_);
lean_dec_ref_known(v___x_2792_, 1);
if (lean_obj_tag(v_val_2793_) == 2)
{
lean_object* v_n_2794_; lean_object* v_mantissa_2795_; lean_object* v_exponent_2796_; uint8_t v_isNeg_2797_; 
v_n_2794_ = lean_ctor_get(v_val_2793_, 0);
lean_inc_ref(v_n_2794_);
lean_dec_ref_known(v_val_2793_, 1);
v_mantissa_2795_ = lean_ctor_get(v_n_2794_, 0);
lean_inc(v_mantissa_2795_);
v_exponent_2796_ = lean_ctor_get(v_n_2794_, 1);
lean_inc(v_exponent_2796_);
lean_dec_ref(v_n_2794_);
v_isNeg_2797_ = lean_int_dec_lt(v_mantissa_2795_, v_intZero_2776_);
if (v_isNeg_2797_ == 0)
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_eq(v_exponent_2796_, v_natZero_2775_);
lean_dec(v_exponent_2796_);
if (v___x_2798_ == 0)
{
lean_dec(v_mantissa_2795_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2763_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2800_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2751_, v___x_2799_);
if (lean_obj_tag(v___x_2800_) == 1)
{
lean_object* v_val_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2934_; 
v_val_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2934_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_val_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2934_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_val_2801_) == 4)
{
lean_object* v_elems_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2933_; 
v_elems_2805_ = lean_ctor_get(v_val_2801_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_val_2801_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2807_ = v_val_2801_;
v_isShared_2808_ = v_isSharedCheck_2933_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_elems_2805_);
lean_dec(v_val_2801_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2933_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_nameMap_2809_; lean_object* v_a_2810_; lean_object* v___x_2811_; 
v_nameMap_2809_ = lean_ctor_get(v_a_2752_, 1);
v_a_2810_ = lean_nat_abs(v_mantissa_2773_);
lean_dec(v_mantissa_2773_);
v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2809_, v_a_2810_);
if (lean_obj_tag(v___x_2811_) == 1)
{
lean_object* v_val_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2810_);
lean_del_object(v___x_2807_);
lean_del_object(v___x_2803_);
v_val_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2923_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_val_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2923_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_a_2816_; lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2816_ = lean_nat_abs(v_mantissa_2787_);
lean_dec(v_mantissa_2787_);
v_a_2817_ = lean_nat_abs(v_mantissa_2795_);
lean_dec(v_mantissa_2795_);
v___x_2818_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2782_, v_a_2752_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2914_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2914_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2914_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_snd_2823_; lean_object* v_fst_2824_; lean_object* v_exprMap_2825_; lean_object* v___x_2826_; 
v_snd_2823_ = lean_ctor_get(v_a_2819_, 1);
lean_inc(v_snd_2823_);
v_fst_2824_ = lean_ctor_get(v_a_2819_, 0);
lean_inc(v_fst_2824_);
lean_dec(v_a_2819_);
v_exprMap_2825_ = lean_ctor_get(v_snd_2823_, 3);
v___x_2826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2825_, v_a_2816_);
if (lean_obj_tag(v___x_2826_) == 1)
{
lean_object* v_val_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v_a_2816_);
lean_del_object(v___x_2814_);
v_val_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2904_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_val_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2904_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2825_, v_a_2817_);
if (lean_obj_tag(v___x_2831_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2894_; 
lean_del_object(v___x_2829_);
lean_del_object(v___x_2821_);
lean_dec(v_a_2817_);
v_val_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2894_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2894_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2805_, v_snd_2823_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2885_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2885_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2885_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_snd_2841_; lean_object* v_fst_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2884_; 
v_snd_2841_ = lean_ctor_get(v_a_2837_, 1);
v_fst_2842_ = lean_ctor_get(v_a_2837_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_a_2837_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2844_ = v_a_2837_;
v_isShared_2845_ = v_isSharedCheck_2884_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snd_2841_);
lean_inc(v_fst_2842_);
lean_dec(v_a_2837_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2884_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_stream_2846_; lean_object* v_nameMap_2847_; lean_object* v_levelMap_2848_; lean_object* v_exprMap_2849_; lean_object* v_recursorRuleMap_2850_; lean_object* v_constMap_2851_; lean_object* v_constOrder_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2883_; 
v_stream_2846_ = lean_ctor_get(v_snd_2841_, 0);
v_nameMap_2847_ = lean_ctor_get(v_snd_2841_, 1);
v_levelMap_2848_ = lean_ctor_get(v_snd_2841_, 2);
v_exprMap_2849_ = lean_ctor_get(v_snd_2841_, 3);
v_recursorRuleMap_2850_ = lean_ctor_get(v_snd_2841_, 4);
v_constMap_2851_ = lean_ctor_get(v_snd_2841_, 5);
v_constOrder_2852_ = lean_ctor_get(v_snd_2841_, 6);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_snd_2841_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2854_ = v_snd_2841_;
v_isShared_2855_ = v_isSharedCheck_2883_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_constOrder_2852_);
lean_inc(v_constMap_2851_);
lean_inc(v_recursorRuleMap_2850_);
lean_inc(v_exprMap_2849_);
lean_inc(v_levelMap_2848_);
lean_inc(v_nameMap_2847_);
lean_inc(v_stream_2846_);
lean_dec(v_snd_2841_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2883_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
uint8_t v___x_2856_; 
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2851_, v_val_2812_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_inc(v_val_2812_);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v_val_2812_);
lean_ctor_set(v___x_2857_, 1, v_fst_2824_);
lean_ctor_set(v___x_2857_, 2, v_val_2827_);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v_val_2832_);
lean_ctor_set(v___x_2858_, 2, v_fst_2842_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 2);
lean_ctor_set(v___x_2834_, 0, v___x_2858_);
v___x_2860_ = v___x_2834_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2861_ = lean_box(0);
lean_inc(v_val_2812_);
v___x_2862_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2851_, v_val_2812_, v___x_2860_);
v___x_2863_ = lean_array_push(v_constOrder_2852_, v_val_2812_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 6, v___x_2863_);
lean_ctor_set(v___x_2854_, 5, v___x_2862_);
v___x_2865_ = v___x_2854_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_stream_2846_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_nameMap_2847_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_levelMap_2848_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_exprMap_2849_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_recursorRuleMap_2850_);
lean_ctor_set(v_reuseFailAlloc_2872_, 5, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2872_, 6, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2865_);
lean_ctor_set(v___x_2844_, 0, v___x_2861_);
v___x_2867_ = v___x_2844_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2867_);
v___x_2869_ = v___x_2839_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
lean_del_object(v___x_2854_);
lean_dec_ref(v_constOrder_2852_);
lean_dec_ref(v_constMap_2851_);
lean_dec_ref(v_recursorRuleMap_2850_);
lean_dec_ref(v_exprMap_2849_);
lean_dec_ref(v_levelMap_2848_);
lean_dec_ref(v_nameMap_2847_);
lean_dec_ref(v_stream_2846_);
lean_del_object(v___x_2844_);
lean_dec(v_fst_2842_);
lean_dec(v_val_2832_);
lean_dec(v_val_2827_);
lean_dec(v_fst_2824_);
v___x_2874_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2875_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2812_, v___x_2856_);
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
lean_dec_ref(v___x_2875_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 18);
lean_ctor_set(v___x_2834_, 0, v___x_2876_);
v___x_2878_ = v___x_2834_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 1);
lean_ctor_set(v___x_2839_, 0, v___x_2878_);
v___x_2880_ = v___x_2839_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_del_object(v___x_2834_);
lean_dec(v_val_2832_);
lean_dec(v_val_2827_);
lean_dec(v_fst_2824_);
lean_dec(v_val_2812_);
v_a_2886_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2836_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2836_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_dec(v___x_2831_);
lean_dec(v_val_2827_);
lean_dec(v_fst_2824_);
lean_dec(v_snd_2823_);
lean_dec(v_val_2812_);
lean_dec_ref(v_elems_2805_);
v___x_2895_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2896_ = l_Nat_reprFast(v_a_2817_);
v___x_2897_ = lean_string_append(v___x_2895_, v___x_2896_);
lean_dec_ref(v___x_2896_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 18);
lean_ctor_set(v___x_2829_, 0, v___x_2897_);
v___x_2899_ = v___x_2829_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2901_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2899_);
v___x_2901_ = v___x_2821_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v___x_2826_);
lean_dec(v_fst_2824_);
lean_dec(v_snd_2823_);
lean_dec(v_a_2817_);
lean_dec(v_val_2812_);
lean_dec_ref(v_elems_2805_);
v___x_2905_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2906_ = l_Nat_reprFast(v_a_2816_);
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
lean_dec_ref(v___x_2906_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 18);
lean_ctor_set(v___x_2814_, 0, v___x_2907_);
v___x_2909_ = v___x_2814_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2909_);
v___x_2911_ = v___x_2821_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2816_);
lean_del_object(v___x_2814_);
lean_dec(v_val_2812_);
lean_dec_ref(v_elems_2805_);
v_a_2915_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2818_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2818_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
lean_dec(v___x_2811_);
lean_dec_ref(v_elems_2805_);
lean_dec(v_mantissa_2795_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec_ref(v_a_2752_);
v___x_2924_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2925_ = l_Nat_reprFast(v_a_2810_);
v___x_2926_ = lean_string_append(v___x_2924_, v___x_2925_);
lean_dec_ref(v___x_2925_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 18);
lean_ctor_set(v___x_2807_, 0, v___x_2926_);
v___x_2928_ = v___x_2807_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2928_);
v___x_2930_ = v___x_2803_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_del_object(v___x_2803_);
lean_dec(v_val_2801_);
lean_dec(v_mantissa_2795_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2766_;
}
}
}
else
{
lean_dec(v___x_2800_);
lean_dec(v_mantissa_2795_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2766_;
}
}
}
else
{
lean_dec(v_exponent_2796_);
lean_dec(v_mantissa_2795_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2763_;
}
}
else
{
lean_dec(v_val_2793_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2763_;
}
}
else
{
lean_dec(v___x_2792_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2763_;
}
}
}
else
{
lean_dec(v_exponent_2788_);
lean_dec(v_mantissa_2787_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2760_;
}
}
else
{
lean_dec(v_val_2785_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2760_;
}
}
else
{
lean_dec(v___x_2784_);
lean_dec_ref(v_elems_2782_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2760_;
}
}
else
{
lean_dec(v_val_2781_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2757_;
}
}
else
{
lean_dec(v___x_2780_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2757_;
}
}
}
else
{
lean_dec(v_exponent_2774_);
lean_dec(v_mantissa_2773_);
lean_dec_ref(v_a_2752_);
goto v___jp_2754_;
}
}
else
{
lean_dec(v_val_2771_);
lean_dec_ref(v_a_2752_);
goto v___jp_2754_;
}
}
else
{
lean_dec(v___x_2770_);
lean_dec_ref(v_a_2752_);
goto v___jp_2754_;
}
v___jp_2754_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
v___jp_2757_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
return v___x_2759_;
}
v___jp_2760_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
v___jp_2763_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
return v___x_2765_;
}
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___boxed(lean_object* v_data_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_data_2935_, v_a_2936_);
lean_dec(v_data_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(lean_object* v_data_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 1)
{
lean_object* v_val_2962_; 
v_val_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_val_2962_);
lean_dec_ref_known(v___x_2961_, 1);
if (lean_obj_tag(v_val_2962_) == 2)
{
lean_object* v_n_2963_; lean_object* v_mantissa_2964_; lean_object* v_exponent_2965_; lean_object* v_natZero_2966_; lean_object* v_intZero_2967_; uint8_t v_isNeg_2968_; 
v_n_2963_ = lean_ctor_get(v_val_2962_, 0);
lean_inc_ref(v_n_2963_);
lean_dec_ref_known(v_val_2962_, 1);
v_mantissa_2964_ = lean_ctor_get(v_n_2963_, 0);
lean_inc(v_mantissa_2964_);
v_exponent_2965_ = lean_ctor_get(v_n_2963_, 1);
lean_inc(v_exponent_2965_);
lean_dec_ref(v_n_2963_);
v_natZero_2966_ = lean_unsigned_to_nat(0u);
v_intZero_2967_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2968_ = lean_int_dec_lt(v_mantissa_2964_, v_intZero_2967_);
if (v_isNeg_2968_ == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = lean_nat_dec_eq(v_exponent_2965_, v_natZero_2966_);
lean_dec(v_exponent_2965_);
if (v___x_2969_ == 0)
{
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2957_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_2970_);
if (lean_obj_tag(v___x_2971_) == 1)
{
lean_object* v_val_2972_; 
v_val_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_val_2972_);
lean_dec_ref_known(v___x_2971_, 1);
if (lean_obj_tag(v_val_2972_) == 4)
{
lean_object* v_elems_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_elems_2973_ = lean_ctor_get(v_val_2972_, 0);
lean_inc_ref(v_elems_2973_);
lean_dec_ref_known(v_val_2972_, 1);
v___x_2974_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2975_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 1)
{
lean_object* v_val_2976_; 
v_val_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___x_2975_, 1);
if (lean_obj_tag(v_val_2976_) == 2)
{
lean_object* v_n_2977_; lean_object* v_mantissa_2978_; lean_object* v_exponent_2979_; uint8_t v_isNeg_2980_; 
v_n_2977_ = lean_ctor_get(v_val_2976_, 0);
lean_inc_ref(v_n_2977_);
lean_dec_ref_known(v_val_2976_, 1);
v_mantissa_2978_ = lean_ctor_get(v_n_2977_, 0);
lean_inc(v_mantissa_2978_);
v_exponent_2979_ = lean_ctor_get(v_n_2977_, 1);
lean_inc(v_exponent_2979_);
lean_dec_ref(v_n_2977_);
v_isNeg_2980_ = lean_int_dec_lt(v_mantissa_2978_, v_intZero_2967_);
if (v_isNeg_2980_ == 0)
{
uint8_t v___x_2981_; 
v___x_2981_ = lean_nat_dec_eq(v_exponent_2979_, v_natZero_2966_);
lean_dec(v_exponent_2979_);
if (v___x_2981_ == 0)
{
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2951_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_object* v_val_2984_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v___x_2983_, 1);
if (lean_obj_tag(v_val_2984_) == 2)
{
lean_object* v_n_2985_; lean_object* v_mantissa_2986_; lean_object* v_exponent_2987_; uint8_t v_isNeg_2988_; 
v_n_2985_ = lean_ctor_get(v_val_2984_, 0);
lean_inc_ref(v_n_2985_);
lean_dec_ref_known(v_val_2984_, 1);
v_mantissa_2986_ = lean_ctor_get(v_n_2985_, 0);
lean_inc(v_mantissa_2986_);
v_exponent_2987_ = lean_ctor_get(v_n_2985_, 1);
lean_inc(v_exponent_2987_);
lean_dec_ref(v_n_2985_);
v_isNeg_2988_ = lean_int_dec_lt(v_mantissa_2986_, v_intZero_2967_);
if (v_isNeg_2988_ == 0)
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_nat_dec_eq(v_exponent_2987_, v_natZero_2966_);
lean_dec(v_exponent_2987_);
if (v___x_2989_ == 0)
{
lean_dec(v_mantissa_2986_);
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2948_;
}
else
{
lean_object* v_a_2990_; lean_object* v_a_2991_; lean_object* v_a_2992_; uint8_t v_b_2994_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_a_2990_ = lean_nat_abs(v_mantissa_2964_);
lean_dec(v_mantissa_2964_);
v_a_2991_ = lean_nat_abs(v_mantissa_2978_);
lean_dec(v_mantissa_2978_);
v_a_2992_ = lean_nat_abs(v_mantissa_2986_);
lean_dec(v_mantissa_2986_);
v___x_3128_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_3128_);
if (lean_obj_tag(v___x_3129_) == 0)
{
v_b_2994_ = v_isNeg_2988_;
goto v___jp_2993_;
}
else
{
lean_object* v_val_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3139_; 
v_val_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_val_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
if (lean_obj_tag(v_val_3130_) == 1)
{
uint8_t v_b_3134_; 
lean_del_object(v___x_3132_);
v_b_3134_ = lean_ctor_get_uint8(v_val_3130_, 0);
lean_dec_ref_known(v_val_3130_, 0);
v_b_2994_ = v_b_3134_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_dec(v_val_3130_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_elems_2973_);
lean_dec_ref(v_a_2943_);
v___x_3135_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3135_);
v___x_3137_ = v___x_3132_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
v___jp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2996_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2942_, v___x_2995_);
if (lean_obj_tag(v___x_2996_) == 1)
{
lean_object* v_val_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3127_; 
v_val_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3127_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_val_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3127_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
if (lean_obj_tag(v_val_2997_) == 4)
{
lean_object* v_elems_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3126_; 
v_elems_3001_ = lean_ctor_get(v_val_2997_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_val_2997_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3003_ = v_val_2997_;
v_isShared_3004_ = v_isSharedCheck_3126_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_elems_3001_);
lean_dec(v_val_2997_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3126_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_nameMap_3005_; lean_object* v___x_3006_; 
v_nameMap_3005_ = lean_ctor_get(v_a_2943_, 1);
v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3005_, v_a_2990_);
if (lean_obj_tag(v___x_3006_) == 1)
{
lean_object* v_val_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3003_);
lean_del_object(v___x_2999_);
lean_dec(v_a_2990_);
v_val_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3116_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_val_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3116_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2973_, v_a_2943_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3107_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3107_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3107_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_snd_3016_; lean_object* v_fst_3017_; lean_object* v_exprMap_3018_; lean_object* v___x_3019_; 
v_snd_3016_ = lean_ctor_get(v_a_3012_, 1);
lean_inc(v_snd_3016_);
v_fst_3017_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_fst_3017_);
lean_dec(v_a_3012_);
v_exprMap_3018_ = lean_ctor_get(v_snd_3016_, 3);
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3018_, v_a_2991_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3097_; 
lean_del_object(v___x_3009_);
lean_dec(v_a_2991_);
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3097_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_val_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3097_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3018_, v_a_2992_);
if (lean_obj_tag(v___x_3024_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3087_; 
lean_del_object(v___x_3022_);
lean_del_object(v___x_3014_);
lean_dec(v_a_2992_);
v_val_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3087_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_val_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3087_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; 
v___x_3029_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3001_, v_snd_3016_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3078_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3078_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3078_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v_snd_3034_; lean_object* v_fst_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3077_; 
v_snd_3034_ = lean_ctor_get(v_a_3030_, 1);
v_fst_3035_ = lean_ctor_get(v_a_3030_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_a_3030_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3037_ = v_a_3030_;
v_isShared_3038_ = v_isSharedCheck_3077_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_snd_3034_);
lean_inc(v_fst_3035_);
lean_dec(v_a_3030_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3077_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v_stream_3039_; lean_object* v_nameMap_3040_; lean_object* v_levelMap_3041_; lean_object* v_exprMap_3042_; lean_object* v_recursorRuleMap_3043_; lean_object* v_constMap_3044_; lean_object* v_constOrder_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3076_; 
v_stream_3039_ = lean_ctor_get(v_snd_3034_, 0);
v_nameMap_3040_ = lean_ctor_get(v_snd_3034_, 1);
v_levelMap_3041_ = lean_ctor_get(v_snd_3034_, 2);
v_exprMap_3042_ = lean_ctor_get(v_snd_3034_, 3);
v_recursorRuleMap_3043_ = lean_ctor_get(v_snd_3034_, 4);
v_constMap_3044_ = lean_ctor_get(v_snd_3034_, 5);
v_constOrder_3045_ = lean_ctor_get(v_snd_3034_, 6);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_snd_3034_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3047_ = v_snd_3034_;
v_isShared_3048_ = v_isSharedCheck_3076_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_constOrder_3045_);
lean_inc(v_constMap_3044_);
lean_inc(v_recursorRuleMap_3043_);
lean_inc(v_exprMap_3042_);
lean_inc(v_levelMap_3041_);
lean_inc(v_nameMap_3040_);
lean_inc(v_stream_3039_);
lean_dec(v_snd_3034_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3076_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
uint8_t v___x_3049_; 
v___x_3049_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3044_, v_val_3007_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_inc(v_val_3007_);
v___x_3050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3050_, 0, v_val_3007_);
lean_ctor_set(v___x_3050_, 1, v_fst_3017_);
lean_ctor_set(v___x_3050_, 2, v_val_3020_);
v___x_3051_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_val_3025_);
lean_ctor_set(v___x_3051_, 2, v_fst_3035_);
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*3, v_b_2994_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 3);
lean_ctor_set(v___x_3027_, 0, v___x_3051_);
v___x_3053_ = v___x_3027_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3054_ = lean_box(0);
lean_inc(v_val_3007_);
v___x_3055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3044_, v_val_3007_, v___x_3053_);
v___x_3056_ = lean_array_push(v_constOrder_3045_, v_val_3007_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 6, v___x_3056_);
lean_ctor_set(v___x_3047_, 5, v___x_3055_);
v___x_3058_ = v___x_3047_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_stream_3039_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_nameMap_3040_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_levelMap_3041_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_exprMap_3042_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_recursorRuleMap_3043_);
lean_ctor_set(v_reuseFailAlloc_3065_, 5, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3065_, 6, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3058_);
lean_ctor_set(v___x_3037_, 0, v___x_3054_);
v___x_3060_ = v___x_3037_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3060_);
v___x_3062_ = v___x_3032_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_del_object(v___x_3047_);
lean_dec_ref(v_constOrder_3045_);
lean_dec_ref(v_constMap_3044_);
lean_dec_ref(v_recursorRuleMap_3043_);
lean_dec_ref(v_exprMap_3042_);
lean_dec_ref(v_levelMap_3041_);
lean_dec_ref(v_nameMap_3040_);
lean_dec_ref(v_stream_3039_);
lean_del_object(v___x_3037_);
lean_dec(v_fst_3035_);
lean_dec(v_val_3025_);
lean_dec(v_val_3020_);
lean_dec(v_fst_3017_);
v___x_3067_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3007_, v___x_3049_);
v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
lean_dec_ref(v___x_3068_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 18);
lean_ctor_set(v___x_3027_, 0, v___x_3069_);
v___x_3071_ = v___x_3027_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 1);
lean_ctor_set(v___x_3032_, 0, v___x_3071_);
v___x_3073_ = v___x_3032_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_del_object(v___x_3027_);
lean_dec(v_val_3025_);
lean_dec(v_val_3020_);
lean_dec(v_fst_3017_);
lean_dec(v_val_3007_);
v_a_3079_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3029_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3029_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
lean_dec(v___x_3024_);
lean_dec(v_val_3020_);
lean_dec(v_fst_3017_);
lean_dec(v_snd_3016_);
lean_dec(v_val_3007_);
lean_dec_ref(v_elems_3001_);
v___x_3088_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3089_ = l_Nat_reprFast(v_a_2992_);
v___x_3090_ = lean_string_append(v___x_3088_, v___x_3089_);
lean_dec_ref(v___x_3089_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set_tag(v___x_3022_, 18);
lean_ctor_set(v___x_3022_, 0, v___x_3090_);
v___x_3092_ = v___x_3022_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3092_);
v___x_3094_ = v___x_3014_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
lean_dec(v___x_3019_);
lean_dec(v_fst_3017_);
lean_dec(v_snd_3016_);
lean_dec(v_val_3007_);
lean_dec_ref(v_elems_3001_);
lean_dec(v_a_2992_);
v___x_3098_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3099_ = l_Nat_reprFast(v_a_2991_);
v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
lean_dec_ref(v___x_3099_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 18);
lean_ctor_set(v___x_3009_, 0, v___x_3100_);
v___x_3102_ = v___x_3009_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3102_);
v___x_3104_ = v___x_3014_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_3009_);
lean_dec(v_val_3007_);
lean_dec_ref(v_elems_3001_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
v_a_3108_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3011_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3011_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
lean_dec(v___x_3006_);
lean_dec_ref(v_elems_3001_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_elems_2973_);
lean_dec_ref(v_a_2943_);
v___x_3117_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3118_ = l_Nat_reprFast(v_a_2990_);
v___x_3119_ = lean_string_append(v___x_3117_, v___x_3118_);
lean_dec_ref(v___x_3118_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 18);
lean_ctor_set(v___x_3003_, 0, v___x_3119_);
v___x_3121_ = v___x_3003_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3123_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3121_);
v___x_3123_ = v___x_2999_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_del_object(v___x_2999_);
lean_dec(v_val_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_elems_2973_);
lean_dec_ref(v_a_2943_);
goto v___jp_2945_;
}
}
}
else
{
lean_dec(v___x_2996_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_elems_2973_);
lean_dec_ref(v_a_2943_);
goto v___jp_2945_;
}
}
}
}
else
{
lean_dec(v_exponent_2987_);
lean_dec(v_mantissa_2986_);
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2948_;
}
}
else
{
lean_dec(v_val_2984_);
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2948_;
}
}
else
{
lean_dec(v___x_2983_);
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2948_;
}
}
}
else
{
lean_dec(v_exponent_2979_);
lean_dec(v_mantissa_2978_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2951_;
}
}
else
{
lean_dec(v_val_2976_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2951_;
}
}
else
{
lean_dec(v___x_2975_);
lean_dec_ref(v_elems_2973_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2951_;
}
}
else
{
lean_dec(v_val_2972_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2954_;
}
}
else
{
lean_dec(v___x_2971_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2954_;
}
}
}
else
{
lean_dec(v_exponent_2965_);
lean_dec(v_mantissa_2964_);
lean_dec_ref(v_a_2943_);
goto v___jp_2957_;
}
}
else
{
lean_dec(v_val_2962_);
lean_dec_ref(v_a_2943_);
goto v___jp_2957_;
}
}
else
{
lean_dec(v___x_2961_);
lean_dec_ref(v_a_2943_);
goto v___jp_2957_;
}
v___jp_2945_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
return v___x_2947_;
}
v___jp_2948_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
v___jp_2951_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
v___jp_2954_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
v___jp_2957_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___boxed(lean_object* v_data_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_data_3140_, v_a_3141_);
lean_dec(v_data_3140_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(lean_object* v_data_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3168_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3152_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 1)
{
lean_object* v_val_3169_; 
v_val_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v___x_3168_, 1);
if (lean_obj_tag(v_val_3169_) == 2)
{
lean_object* v_n_3170_; lean_object* v_mantissa_3171_; lean_object* v_exponent_3172_; lean_object* v_natZero_3173_; lean_object* v_intZero_3174_; uint8_t v_isNeg_3175_; 
v_n_3170_ = lean_ctor_get(v_val_3169_, 0);
lean_inc_ref(v_n_3170_);
lean_dec_ref_known(v_val_3169_, 1);
v_mantissa_3171_ = lean_ctor_get(v_n_3170_, 0);
lean_inc(v_mantissa_3171_);
v_exponent_3172_ = lean_ctor_get(v_n_3170_, 1);
lean_inc(v_exponent_3172_);
lean_dec_ref(v_n_3170_);
v_natZero_3173_ = lean_unsigned_to_nat(0u);
v_intZero_3174_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3175_ = lean_int_dec_lt(v_mantissa_3171_, v_intZero_3174_);
if (v_isNeg_3175_ == 0)
{
uint8_t v___x_3176_; 
v___x_3176_ = lean_nat_dec_eq(v_exponent_3172_, v_natZero_3173_);
lean_dec(v_exponent_3172_);
if (v___x_3176_ == 0)
{
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3164_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3152_, v___x_3177_);
if (lean_obj_tag(v___x_3178_) == 1)
{
lean_object* v_val_3179_; 
v_val_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_val_3179_);
lean_dec_ref_known(v___x_3178_, 1);
if (lean_obj_tag(v_val_3179_) == 4)
{
lean_object* v_elems_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_elems_3180_ = lean_ctor_get(v_val_3179_, 0);
lean_inc_ref(v_elems_3180_);
lean_dec_ref_known(v_val_3179_, 1);
v___x_3181_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3152_, v___x_3181_);
if (lean_obj_tag(v___x_3182_) == 1)
{
lean_object* v_val_3183_; 
v_val_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v___x_3182_, 1);
if (lean_obj_tag(v_val_3183_) == 2)
{
lean_object* v_n_3184_; lean_object* v_mantissa_3185_; lean_object* v_exponent_3186_; uint8_t v_isNeg_3187_; 
v_n_3184_ = lean_ctor_get(v_val_3183_, 0);
lean_inc_ref(v_n_3184_);
lean_dec_ref_known(v_val_3183_, 1);
v_mantissa_3185_ = lean_ctor_get(v_n_3184_, 0);
lean_inc(v_mantissa_3185_);
v_exponent_3186_ = lean_ctor_get(v_n_3184_, 1);
lean_inc(v_exponent_3186_);
lean_dec_ref(v_n_3184_);
v_isNeg_3187_ = lean_int_dec_lt(v_mantissa_3185_, v_intZero_3174_);
if (v_isNeg_3187_ == 0)
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_nat_dec_eq(v_exponent_3186_, v_natZero_3173_);
lean_dec(v_exponent_3186_);
if (v___x_3188_ == 0)
{
lean_dec(v_mantissa_3185_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3158_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2));
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3152_, v___x_3189_);
if (lean_obj_tag(v___x_3190_) == 1)
{
lean_object* v_val_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3319_; 
v_val_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3319_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_val_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3319_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
if (lean_obj_tag(v_val_3191_) == 3)
{
lean_object* v_s_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3318_; 
v_s_3195_ = lean_ctor_get(v_val_3191_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_val_3191_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3197_ = v_val_3191_;
v_isShared_3198_ = v_isSharedCheck_3318_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_s_3195_);
lean_dec(v_val_3191_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3318_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_nameMap_3199_; lean_object* v_a_3200_; lean_object* v___x_3201_; 
v_nameMap_3199_ = lean_ctor_get(v_a_3153_, 1);
v_a_3200_ = lean_nat_abs(v_mantissa_3171_);
lean_dec(v_mantissa_3171_);
v___x_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3199_, v_a_3200_);
if (lean_obj_tag(v___x_3201_) == 1)
{
lean_object* v_val_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_a_3200_);
lean_del_object(v___x_3193_);
v_val_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3308_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_val_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3308_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_a_3206_; lean_object* v___x_3207_; 
v_a_3206_ = lean_nat_abs(v_mantissa_3185_);
lean_dec(v_mantissa_3185_);
v___x_3207_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3180_, v_a_3153_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3299_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3299_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3299_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_snd_3212_; lean_object* v_fst_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3298_; 
v_snd_3212_ = lean_ctor_get(v_a_3208_, 1);
v_fst_3213_ = lean_ctor_get(v_a_3208_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_a_3208_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3215_ = v_a_3208_;
v_isShared_3216_ = v_isSharedCheck_3298_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_snd_3212_);
lean_inc(v_fst_3213_);
lean_dec(v_a_3208_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3298_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v_stream_3217_; lean_object* v_nameMap_3218_; lean_object* v_levelMap_3219_; lean_object* v_exprMap_3220_; lean_object* v_recursorRuleMap_3221_; lean_object* v_constMap_3222_; lean_object* v_constOrder_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3297_; 
v_stream_3217_ = lean_ctor_get(v_snd_3212_, 0);
v_nameMap_3218_ = lean_ctor_get(v_snd_3212_, 1);
v_levelMap_3219_ = lean_ctor_get(v_snd_3212_, 2);
v_exprMap_3220_ = lean_ctor_get(v_snd_3212_, 3);
v_recursorRuleMap_3221_ = lean_ctor_get(v_snd_3212_, 4);
v_constMap_3222_ = lean_ctor_get(v_snd_3212_, 5);
v_constOrder_3223_ = lean_ctor_get(v_snd_3212_, 6);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_snd_3212_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3225_ = v_snd_3212_;
v_isShared_3226_ = v_isSharedCheck_3297_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_constOrder_3223_);
lean_inc(v_constMap_3222_);
lean_inc(v_recursorRuleMap_3221_);
lean_inc(v_exprMap_3220_);
lean_inc(v_levelMap_3219_);
lean_inc(v_nameMap_3218_);
lean_inc(v_stream_3217_);
lean_dec(v_snd_3212_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3297_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3220_, v_a_3206_);
if (lean_obj_tag(v___x_3227_) == 1)
{
lean_object* v_val_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_a_3206_);
v_val_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3287_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_val_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3287_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
uint8_t v_kind_3233_; lean_object* v_stream_3234_; lean_object* v_nameMap_3235_; lean_object* v_levelMap_3236_; lean_object* v_exprMap_3237_; lean_object* v_recursorRuleMap_3238_; lean_object* v_constMap_3239_; lean_object* v_constOrder_3240_; uint8_t v___x_3268_; 
v___x_3268_ = lean_string_dec_eq(v_s_3195_, v___x_3181_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3270_ = lean_string_dec_eq(v_s_3195_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4));
v___x_3272_ = lean_string_dec_eq(v_s_3195_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5));
v___x_3274_ = lean_string_dec_eq(v_s_3195_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_del_object(v___x_3230_);
lean_dec(v_val_3228_);
lean_del_object(v___x_3225_);
lean_dec_ref(v_constOrder_3223_);
lean_dec_ref(v_constMap_3222_);
lean_dec_ref(v_recursorRuleMap_3221_);
lean_dec_ref(v_exprMap_3220_);
lean_dec_ref(v_levelMap_3219_);
lean_dec_ref(v_nameMap_3218_);
lean_dec_ref(v_stream_3217_);
lean_del_object(v___x_3215_);
lean_dec(v_fst_3213_);
lean_del_object(v___x_3210_);
lean_dec(v_val_3202_);
v___x_3275_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6));
v___x_3276_ = lean_string_append(v___x_3275_, v_s_3195_);
lean_dec_ref(v_s_3195_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 18);
lean_ctor_set(v___x_3204_, 0, v___x_3276_);
v___x_3278_ = v___x_3204_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3280_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 1);
lean_ctor_set(v___x_3197_, 0, v___x_3278_);
v___x_3280_ = v___x_3197_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
else
{
uint8_t v___x_3283_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v___x_3283_ = 3;
v_kind_3233_ = v___x_3283_;
v_stream_3234_ = v_stream_3217_;
v_nameMap_3235_ = v_nameMap_3218_;
v_levelMap_3236_ = v_levelMap_3219_;
v_exprMap_3237_ = v_exprMap_3220_;
v_recursorRuleMap_3238_ = v_recursorRuleMap_3221_;
v_constMap_3239_ = v_constMap_3222_;
v_constOrder_3240_ = v_constOrder_3223_;
goto v___jp_3232_;
}
}
else
{
uint8_t v___x_3284_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v___x_3284_ = 2;
v_kind_3233_ = v___x_3284_;
v_stream_3234_ = v_stream_3217_;
v_nameMap_3235_ = v_nameMap_3218_;
v_levelMap_3236_ = v_levelMap_3219_;
v_exprMap_3237_ = v_exprMap_3220_;
v_recursorRuleMap_3238_ = v_recursorRuleMap_3221_;
v_constMap_3239_ = v_constMap_3222_;
v_constOrder_3240_ = v_constOrder_3223_;
goto v___jp_3232_;
}
}
else
{
uint8_t v___x_3285_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v___x_3285_ = 1;
v_kind_3233_ = v___x_3285_;
v_stream_3234_ = v_stream_3217_;
v_nameMap_3235_ = v_nameMap_3218_;
v_levelMap_3236_ = v_levelMap_3219_;
v_exprMap_3237_ = v_exprMap_3220_;
v_recursorRuleMap_3238_ = v_recursorRuleMap_3221_;
v_constMap_3239_ = v_constMap_3222_;
v_constOrder_3240_ = v_constOrder_3223_;
goto v___jp_3232_;
}
}
else
{
uint8_t v___x_3286_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v___x_3286_ = 0;
v_kind_3233_ = v___x_3286_;
v_stream_3234_ = v_stream_3217_;
v_nameMap_3235_ = v_nameMap_3218_;
v_levelMap_3236_ = v_levelMap_3219_;
v_exprMap_3237_ = v_exprMap_3220_;
v_recursorRuleMap_3238_ = v_recursorRuleMap_3221_;
v_constMap_3239_ = v_constMap_3222_;
v_constOrder_3240_ = v_constOrder_3223_;
goto v___jp_3232_;
}
v___jp_3232_:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3239_, v_val_3202_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
lean_inc(v_val_3202_);
v___x_3242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3242_, 0, v_val_3202_);
lean_ctor_set(v___x_3242_, 1, v_fst_3213_);
lean_ctor_set(v___x_3242_, 2, v_val_3228_);
v___x_3243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*1, v_kind_3233_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 4);
lean_ctor_set(v___x_3230_, 0, v___x_3243_);
v___x_3245_ = v___x_3230_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = lean_box(0);
lean_inc(v_val_3202_);
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3239_, v_val_3202_, v___x_3245_);
v___x_3248_ = lean_array_push(v_constOrder_3240_, v_val_3202_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 6, v___x_3248_);
lean_ctor_set(v___x_3225_, 5, v___x_3247_);
lean_ctor_set(v___x_3225_, 4, v_recursorRuleMap_3238_);
lean_ctor_set(v___x_3225_, 3, v_exprMap_3237_);
lean_ctor_set(v___x_3225_, 2, v_levelMap_3236_);
lean_ctor_set(v___x_3225_, 1, v_nameMap_3235_);
lean_ctor_set(v___x_3225_, 0, v_stream_3234_);
v___x_3250_ = v___x_3225_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_stream_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_nameMap_3235_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_levelMap_3236_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_exprMap_3237_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_recursorRuleMap_3238_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3252_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v___x_3250_);
lean_ctor_set(v___x_3215_, 0, v___x_3246_);
v___x_3252_ = v___x_3215_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3252_);
v___x_3254_ = v___x_3210_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
lean_dec_ref(v_constOrder_3240_);
lean_dec_ref(v_constMap_3239_);
lean_dec_ref(v_recursorRuleMap_3238_);
lean_dec_ref(v_exprMap_3237_);
lean_dec_ref(v_levelMap_3236_);
lean_dec_ref(v_nameMap_3235_);
lean_dec_ref(v_stream_3234_);
lean_dec(v_val_3228_);
lean_del_object(v___x_3225_);
lean_del_object(v___x_3215_);
lean_dec(v_fst_3213_);
v___x_3259_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3202_, v___x_3241_);
v___x_3261_ = lean_string_append(v___x_3259_, v___x_3260_);
lean_dec_ref(v___x_3260_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 18);
lean_ctor_set(v___x_3230_, 0, v___x_3261_);
v___x_3263_ = v___x_3230_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3265_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 1);
lean_ctor_set(v___x_3210_, 0, v___x_3263_);
v___x_3265_ = v___x_3210_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
lean_dec(v___x_3227_);
lean_del_object(v___x_3225_);
lean_dec_ref(v_constOrder_3223_);
lean_dec_ref(v_constMap_3222_);
lean_dec_ref(v_recursorRuleMap_3221_);
lean_dec_ref(v_exprMap_3220_);
lean_dec_ref(v_levelMap_3219_);
lean_dec_ref(v_nameMap_3218_);
lean_dec_ref(v_stream_3217_);
lean_del_object(v___x_3215_);
lean_dec(v_fst_3213_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v___x_3288_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3289_ = l_Nat_reprFast(v_a_3206_);
v___x_3290_ = lean_string_append(v___x_3288_, v___x_3289_);
lean_dec_ref(v___x_3289_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 18);
lean_ctor_set(v___x_3204_, 0, v___x_3290_);
v___x_3292_ = v___x_3204_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3294_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 1);
lean_ctor_set(v___x_3210_, 0, v___x_3292_);
v___x_3294_ = v___x_3210_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v_a_3206_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_s_3195_);
v_a_3300_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3207_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3207_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_dec(v___x_3201_);
lean_dec_ref(v_s_3195_);
lean_dec(v_mantissa_3185_);
lean_dec_ref(v_elems_3180_);
lean_dec_ref(v_a_3153_);
v___x_3309_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3310_ = l_Nat_reprFast(v_a_3200_);
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
lean_dec_ref(v___x_3310_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 18);
lean_ctor_set(v___x_3197_, 0, v___x_3311_);
v___x_3313_ = v___x_3197_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3313_);
v___x_3315_ = v___x_3193_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
else
{
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_dec(v_mantissa_3185_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3155_;
}
}
}
else
{
lean_dec(v___x_3190_);
lean_dec(v_mantissa_3185_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3155_;
}
}
}
else
{
lean_dec(v_exponent_3186_);
lean_dec(v_mantissa_3185_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3158_;
}
}
else
{
lean_dec(v_val_3183_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3158_;
}
}
else
{
lean_dec(v___x_3182_);
lean_dec_ref(v_elems_3180_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3158_;
}
}
else
{
lean_dec(v_val_3179_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3161_;
}
}
else
{
lean_dec(v___x_3178_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3161_;
}
}
}
else
{
lean_dec(v_exponent_3172_);
lean_dec(v_mantissa_3171_);
lean_dec_ref(v_a_3153_);
goto v___jp_3164_;
}
}
else
{
lean_dec(v_val_3169_);
lean_dec_ref(v_a_3153_);
goto v___jp_3164_;
}
}
else
{
lean_dec(v___x_3168_);
lean_dec_ref(v_a_3153_);
goto v___jp_3164_;
}
v___jp_3155_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
v___jp_3158_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
v___jp_3161_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
v___jp_3164_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___boxed(lean_object* v_data_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_data_3320_, v_a_3321_);
lean_dec(v_data_3320_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(lean_object* v_json_3336_, lean_object* v_a_3337_){
_start:
{
if (lean_obj_tag(v_json_3336_) == 5)
{
lean_object* v_kvPairs_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_kvPairs_3372_ = lean_ctor_get(v_json_3336_, 0);
v___x_3373_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_val_3375_) == 2)
{
lean_object* v_n_3376_; lean_object* v_mantissa_3377_; lean_object* v_exponent_3378_; lean_object* v_natZero_3379_; lean_object* v_intZero_3380_; uint8_t v_isNeg_3381_; 
v_n_3376_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_n_3376_);
lean_dec_ref_known(v_val_3375_, 1);
v_mantissa_3377_ = lean_ctor_get(v_n_3376_, 0);
lean_inc(v_mantissa_3377_);
v_exponent_3378_ = lean_ctor_get(v_n_3376_, 1);
lean_inc(v_exponent_3378_);
lean_dec_ref(v_n_3376_);
v_natZero_3379_ = lean_unsigned_to_nat(0u);
v_intZero_3380_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3381_ = lean_int_dec_lt(v_mantissa_3377_, v_intZero_3380_);
if (v_isNeg_3381_ == 0)
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_nat_dec_eq(v_exponent_3378_, v_natZero_3379_);
lean_dec(v_exponent_3378_);
if (v___x_3382_ == 0)
{
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3339_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3383_);
if (lean_obj_tag(v___x_3384_) == 1)
{
lean_object* v_val_3385_; 
v_val_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v___x_3384_, 1);
if (lean_obj_tag(v_val_3385_) == 4)
{
lean_object* v_elems_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_elems_3386_ = lean_ctor_get(v_val_3385_, 0);
lean_inc_ref(v_elems_3386_);
lean_dec_ref_known(v_val_3385_, 1);
v___x_3387_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3388_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3387_);
if (lean_obj_tag(v___x_3388_) == 1)
{
lean_object* v_val_3389_; 
v_val_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___x_3388_, 1);
if (lean_obj_tag(v_val_3389_) == 2)
{
lean_object* v_n_3390_; lean_object* v_mantissa_3391_; lean_object* v_exponent_3392_; uint8_t v_isNeg_3393_; 
v_n_3390_ = lean_ctor_get(v_val_3389_, 0);
lean_inc_ref(v_n_3390_);
lean_dec_ref_known(v_val_3389_, 1);
v_mantissa_3391_ = lean_ctor_get(v_n_3390_, 0);
lean_inc(v_mantissa_3391_);
v_exponent_3392_ = lean_ctor_get(v_n_3390_, 1);
lean_inc(v_exponent_3392_);
lean_dec_ref(v_n_3390_);
v_isNeg_3393_ = lean_int_dec_lt(v_mantissa_3391_, v_intZero_3380_);
if (v_isNeg_3393_ == 0)
{
uint8_t v___x_3394_; 
v___x_3394_ = lean_nat_dec_eq(v_exponent_3392_, v_natZero_3379_);
lean_dec(v_exponent_3392_);
if (v___x_3394_ == 0)
{
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3345_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3396_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 1)
{
lean_object* v_val_3397_; 
v_val_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_val_3397_);
lean_dec_ref_known(v___x_3396_, 1);
if (lean_obj_tag(v_val_3397_) == 2)
{
lean_object* v_n_3398_; lean_object* v_mantissa_3399_; lean_object* v_exponent_3400_; uint8_t v_isNeg_3401_; 
v_n_3398_ = lean_ctor_get(v_val_3397_, 0);
lean_inc_ref(v_n_3398_);
lean_dec_ref_known(v_val_3397_, 1);
v_mantissa_3399_ = lean_ctor_get(v_n_3398_, 0);
lean_inc(v_mantissa_3399_);
v_exponent_3400_ = lean_ctor_get(v_n_3398_, 1);
lean_inc(v_exponent_3400_);
lean_dec_ref(v_n_3398_);
v_isNeg_3401_ = lean_int_dec_lt(v_mantissa_3399_, v_intZero_3380_);
if (v_isNeg_3401_ == 0)
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_nat_dec_eq(v_exponent_3400_, v_natZero_3379_);
lean_dec(v_exponent_3400_);
if (v___x_3402_ == 0)
{
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3348_;
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3403_);
if (lean_obj_tag(v___x_3404_) == 1)
{
lean_object* v_val_3405_; 
v_val_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3404_, 1);
if (lean_obj_tag(v_val_3405_) == 2)
{
lean_object* v_n_3406_; lean_object* v_mantissa_3407_; lean_object* v_exponent_3408_; uint8_t v_isNeg_3409_; 
v_n_3406_ = lean_ctor_get(v_val_3405_, 0);
lean_inc_ref(v_n_3406_);
lean_dec_ref_known(v_val_3405_, 1);
v_mantissa_3407_ = lean_ctor_get(v_n_3406_, 0);
lean_inc(v_mantissa_3407_);
v_exponent_3408_ = lean_ctor_get(v_n_3406_, 1);
lean_inc(v_exponent_3408_);
lean_dec_ref(v_n_3406_);
v_isNeg_3409_ = lean_int_dec_lt(v_mantissa_3407_, v_intZero_3380_);
if (v_isNeg_3409_ == 0)
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_nat_dec_eq(v_exponent_3408_, v_natZero_3379_);
lean_dec(v_exponent_3408_);
if (v___x_3410_ == 0)
{
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3351_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3411_);
if (lean_obj_tag(v___x_3412_) == 1)
{
lean_object* v_val_3413_; 
v_val_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v___x_3412_, 1);
if (lean_obj_tag(v_val_3413_) == 4)
{
lean_object* v_elems_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_elems_3414_ = lean_ctor_get(v_val_3413_, 0);
lean_inc_ref(v_elems_3414_);
lean_dec_ref_known(v_val_3413_, 1);
v___x_3415_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_3416_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3415_);
if (lean_obj_tag(v___x_3416_) == 1)
{
lean_object* v_val_3417_; 
v_val_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_val_3417_);
lean_dec_ref_known(v___x_3416_, 1);
if (lean_obj_tag(v_val_3417_) == 4)
{
lean_object* v_elems_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_elems_3418_ = lean_ctor_get(v_val_3417_, 0);
lean_inc_ref(v_elems_3418_);
lean_dec_ref_known(v_val_3417_, 1);
v___x_3419_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5));
v___x_3420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3419_);
if (lean_obj_tag(v___x_3420_) == 1)
{
lean_object* v_val_3421_; 
v_val_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_val_3421_);
lean_dec_ref_known(v___x_3420_, 1);
if (lean_obj_tag(v_val_3421_) == 2)
{
lean_object* v_n_3422_; lean_object* v_mantissa_3423_; lean_object* v_exponent_3424_; uint8_t v_isNeg_3425_; 
v_n_3422_ = lean_ctor_get(v_val_3421_, 0);
lean_inc_ref(v_n_3422_);
lean_dec_ref_known(v_val_3421_, 1);
v_mantissa_3423_ = lean_ctor_get(v_n_3422_, 0);
lean_inc(v_mantissa_3423_);
v_exponent_3424_ = lean_ctor_get(v_n_3422_, 1);
lean_inc(v_exponent_3424_);
lean_dec_ref(v_n_3422_);
v_isNeg_3425_ = lean_int_dec_lt(v_mantissa_3423_, v_intZero_3380_);
if (v_isNeg_3425_ == 0)
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_nat_dec_eq(v_exponent_3424_, v_natZero_3379_);
lean_dec(v_exponent_3424_);
if (v___x_3426_ == 0)
{
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3360_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6));
v___x_3428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 1)
{
lean_object* v_val_3429_; 
v_val_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_val_3429_);
lean_dec_ref_known(v___x_3428_, 1);
if (lean_obj_tag(v_val_3429_) == 1)
{
uint8_t v_b_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_b_3430_ = lean_ctor_get_uint8(v_val_3429_, 0);
lean_dec_ref_known(v_val_3429_, 0);
v___x_3431_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3431_);
if (lean_obj_tag(v___x_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3569_; 
v_val_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3569_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3569_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
if (lean_obj_tag(v_val_3433_) == 1)
{
uint8_t v_b_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_b_3437_ = lean_ctor_get_uint8(v_val_3433_, 0);
lean_dec_ref_known(v_val_3433_, 0);
v___x_3438_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7));
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3372_, v___x_3438_);
if (lean_obj_tag(v___x_3439_) == 1)
{
lean_object* v_val_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3568_; 
v_val_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3568_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_val_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3568_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
if (lean_obj_tag(v_val_3440_) == 1)
{
uint8_t v_b_3444_; lean_object* v_nameMap_3445_; lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_b_3444_ = lean_ctor_get_uint8(v_val_3440_, 0);
lean_dec_ref_known(v_val_3440_, 0);
v_nameMap_3445_ = lean_ctor_get(v_a_3337_, 1);
v_a_3446_ = lean_nat_abs(v_mantissa_3377_);
lean_dec(v_mantissa_3377_);
v___x_3447_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3445_, v_a_3446_);
if (lean_obj_tag(v___x_3447_) == 1)
{
lean_object* v_val_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_a_3446_);
lean_del_object(v___x_3442_);
lean_del_object(v___x_3435_);
v_val_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3558_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_val_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3558_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_a_3452_; lean_object* v_a_3453_; lean_object* v_a_3454_; lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3452_ = lean_nat_abs(v_mantissa_3391_);
lean_dec(v_mantissa_3391_);
v_a_3453_ = lean_nat_abs(v_mantissa_3399_);
lean_dec(v_mantissa_3399_);
v_a_3454_ = lean_nat_abs(v_mantissa_3407_);
lean_dec(v_mantissa_3407_);
v_a_3455_ = lean_nat_abs(v_mantissa_3423_);
lean_dec(v_mantissa_3423_);
v___x_3456_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3386_, v_a_3337_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3549_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3549_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3549_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_snd_3461_; lean_object* v_fst_3462_; lean_object* v_exprMap_3463_; lean_object* v___x_3464_; 
v_snd_3461_ = lean_ctor_get(v_a_3457_, 1);
lean_inc(v_snd_3461_);
v_fst_3462_ = lean_ctor_get(v_a_3457_, 0);
lean_inc(v_fst_3462_);
lean_dec(v_a_3457_);
v_exprMap_3463_ = lean_ctor_get(v_snd_3461_, 3);
v___x_3464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3463_, v_a_3452_);
if (lean_obj_tag(v___x_3464_) == 1)
{
lean_object* v_val_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3539_; 
lean_del_object(v___x_3459_);
lean_dec(v_a_3452_);
lean_del_object(v___x_3450_);
v_val_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3539_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_val_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3539_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; 
v___x_3469_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3414_, v_snd_3461_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v___x_3473_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v_fst_3471_ = lean_ctor_get(v_a_3470_, 0);
lean_inc(v_fst_3471_);
v_snd_3472_ = lean_ctor_get(v_a_3470_, 1);
lean_inc(v_snd_3472_);
lean_dec(v_a_3470_);
v___x_3473_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3418_, v_snd_3472_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3522_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3522_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3522_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_snd_3478_; lean_object* v_fst_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3521_; 
v_snd_3478_ = lean_ctor_get(v_a_3474_, 1);
v_fst_3479_ = lean_ctor_get(v_a_3474_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3481_ = v_a_3474_;
v_isShared_3482_ = v_isSharedCheck_3521_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_snd_3478_);
lean_inc(v_fst_3479_);
lean_dec(v_a_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3521_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_stream_3483_; lean_object* v_nameMap_3484_; lean_object* v_levelMap_3485_; lean_object* v_exprMap_3486_; lean_object* v_recursorRuleMap_3487_; lean_object* v_constMap_3488_; lean_object* v_constOrder_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3520_; 
v_stream_3483_ = lean_ctor_get(v_snd_3478_, 0);
v_nameMap_3484_ = lean_ctor_get(v_snd_3478_, 1);
v_levelMap_3485_ = lean_ctor_get(v_snd_3478_, 2);
v_exprMap_3486_ = lean_ctor_get(v_snd_3478_, 3);
v_recursorRuleMap_3487_ = lean_ctor_get(v_snd_3478_, 4);
v_constMap_3488_ = lean_ctor_get(v_snd_3478_, 5);
v_constOrder_3489_ = lean_ctor_get(v_snd_3478_, 6);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_snd_3478_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3491_ = v_snd_3478_;
v_isShared_3492_ = v_isSharedCheck_3520_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_constOrder_3489_);
lean_inc(v_constMap_3488_);
lean_inc(v_recursorRuleMap_3487_);
lean_inc(v_exprMap_3486_);
lean_inc(v_levelMap_3485_);
lean_inc(v_nameMap_3484_);
lean_inc(v_stream_3483_);
lean_dec(v_snd_3478_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3520_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3488_, v_val_3448_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_inc(v_val_3448_);
v___x_3494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3494_, 0, v_val_3448_);
lean_ctor_set(v___x_3494_, 1, v_fst_3462_);
lean_ctor_set(v___x_3494_, 2, v_val_3465_);
v___x_3495_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v_a_3453_);
lean_ctor_set(v___x_3495_, 2, v_a_3454_);
lean_ctor_set(v___x_3495_, 3, v_fst_3471_);
lean_ctor_set(v___x_3495_, 4, v_fst_3479_);
lean_ctor_set(v___x_3495_, 5, v_a_3455_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*6, v_b_3430_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*6 + 1, v_b_3437_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*6 + 2, v_b_3444_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 5);
lean_ctor_set(v___x_3467_, 0, v___x_3495_);
v___x_3497_ = v___x_3467_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3498_ = lean_box(0);
lean_inc(v_val_3448_);
v___x_3499_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3488_, v_val_3448_, v___x_3497_);
v___x_3500_ = lean_array_push(v_constOrder_3489_, v_val_3448_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 6, v___x_3500_);
lean_ctor_set(v___x_3491_, 5, v___x_3499_);
v___x_3502_ = v___x_3491_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_stream_3483_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_nameMap_3484_);
lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_levelMap_3485_);
lean_ctor_set(v_reuseFailAlloc_3509_, 3, v_exprMap_3486_);
lean_ctor_set(v_reuseFailAlloc_3509_, 4, v_recursorRuleMap_3487_);
lean_ctor_set(v_reuseFailAlloc_3509_, 5, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3509_, 6, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3502_);
lean_ctor_set(v___x_3481_, 0, v___x_3498_);
v___x_3504_ = v___x_3481_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3504_);
v___x_3506_ = v___x_3476_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_del_object(v___x_3491_);
lean_dec_ref(v_constOrder_3489_);
lean_dec_ref(v_constMap_3488_);
lean_dec_ref(v_recursorRuleMap_3487_);
lean_dec_ref(v_exprMap_3486_);
lean_dec_ref(v_levelMap_3485_);
lean_dec_ref(v_nameMap_3484_);
lean_dec_ref(v_stream_3483_);
lean_del_object(v___x_3481_);
lean_dec(v_fst_3479_);
lean_dec(v_fst_3471_);
lean_dec(v_val_3465_);
lean_dec(v_fst_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
v___x_3511_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3512_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3448_, v___x_3493_);
v___x_3513_ = lean_string_append(v___x_3511_, v___x_3512_);
lean_dec_ref(v___x_3512_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 18);
lean_ctor_set(v___x_3467_, 0, v___x_3513_);
v___x_3515_ = v___x_3467_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set_tag(v___x_3476_, 1);
lean_ctor_set(v___x_3476_, 0, v___x_3515_);
v___x_3517_ = v___x_3476_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_fst_3471_);
lean_del_object(v___x_3467_);
lean_dec(v_val_3465_);
lean_dec(v_fst_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec(v_val_3448_);
v_a_3523_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3473_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3473_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_del_object(v___x_3467_);
lean_dec(v_val_3465_);
lean_dec(v_fst_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec(v_val_3448_);
lean_dec_ref(v_elems_3418_);
v_a_3531_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3469_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3469_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_dec(v___x_3464_);
lean_dec(v_fst_3462_);
lean_dec(v_snd_3461_);
lean_dec(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec(v_val_3448_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
v___x_3540_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3541_ = l_Nat_reprFast(v_a_3452_);
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
lean_dec_ref(v___x_3541_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 18);
lean_ctor_set(v___x_3450_, 0, v___x_3542_);
v___x_3544_ = v___x_3450_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3546_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 1);
lean_ctor_set(v___x_3459_, 0, v___x_3544_);
v___x_3546_ = v___x_3459_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec(v_a_3452_);
lean_del_object(v___x_3450_);
lean_dec(v_val_3448_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
v_a_3550_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3456_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3456_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_dec(v___x_3447_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec_ref(v_a_3337_);
v___x_3559_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3560_ = l_Nat_reprFast(v_a_3446_);
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
lean_dec_ref(v___x_3560_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 18);
lean_ctor_set(v___x_3442_, 0, v___x_3561_);
v___x_3563_ = v___x_3442_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3563_);
v___x_3565_ = v___x_3435_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_del_object(v___x_3442_);
lean_dec(v_val_3440_);
lean_del_object(v___x_3435_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3369_;
}
}
}
else
{
lean_dec(v___x_3439_);
lean_del_object(v___x_3435_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3369_;
}
}
else
{
lean_del_object(v___x_3435_);
lean_dec(v_val_3433_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3366_;
}
}
}
else
{
lean_dec(v___x_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3366_;
}
}
else
{
lean_dec(v_val_3429_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3363_;
}
}
else
{
lean_dec(v___x_3428_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3363_;
}
}
}
else
{
lean_dec(v_exponent_3424_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3360_;
}
}
else
{
lean_dec(v_val_3421_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3360_;
}
}
else
{
lean_dec(v___x_3420_);
lean_dec_ref(v_elems_3418_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3360_;
}
}
else
{
lean_dec(v_val_3417_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3357_;
}
}
else
{
lean_dec(v___x_3416_);
lean_dec_ref(v_elems_3414_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3357_;
}
}
else
{
lean_dec(v_val_3413_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3354_;
}
}
else
{
lean_dec(v___x_3412_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3354_;
}
}
}
else
{
lean_dec(v_exponent_3408_);
lean_dec(v_mantissa_3407_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3351_;
}
}
else
{
lean_dec(v_val_3405_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3351_;
}
}
else
{
lean_dec(v___x_3404_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3351_;
}
}
}
else
{
lean_dec(v_exponent_3400_);
lean_dec(v_mantissa_3399_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3348_;
}
}
else
{
lean_dec(v_val_3397_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3348_;
}
}
else
{
lean_dec(v___x_3396_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3348_;
}
}
}
else
{
lean_dec(v_exponent_3392_);
lean_dec(v_mantissa_3391_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3345_;
}
}
else
{
lean_dec(v_val_3389_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3345_;
}
}
else
{
lean_dec(v___x_3388_);
lean_dec_ref(v_elems_3386_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3345_;
}
}
else
{
lean_dec(v_val_3385_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3342_;
}
}
else
{
lean_dec(v___x_3384_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3342_;
}
}
}
else
{
lean_dec(v_exponent_3378_);
lean_dec(v_mantissa_3377_);
lean_dec_ref(v_a_3337_);
goto v___jp_3339_;
}
}
else
{
lean_dec(v_val_3375_);
lean_dec_ref(v_a_3337_);
goto v___jp_3339_;
}
}
else
{
lean_dec(v___x_3374_);
lean_dec_ref(v_a_3337_);
goto v___jp_3339_;
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec_ref(v_a_3337_);
v___x_3570_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9));
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
v___jp_3339_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
v___jp_3342_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
v___jp_3345_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
v___jp_3348_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
v___jp_3351_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
v___jp_3354_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
v___jp_3357_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
v___jp_3360_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
return v___x_3362_;
}
v___jp_3363_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
v___jp_3366_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
v___jp_3369_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___boxed(lean_object* v_json_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v_json_3572_, v_a_3573_);
lean_dec(v_json_3572_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(lean_object* v_json_3582_, lean_object* v_a_3583_){
_start:
{
if (lean_obj_tag(v_json_3582_) == 5)
{
lean_object* v_kvPairs_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v_kvPairs_3609_ = lean_ctor_get(v_json_3582_, 0);
v___x_3610_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3611_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3610_);
if (lean_obj_tag(v___x_3611_) == 1)
{
lean_object* v_val_3612_; 
v_val_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_val_3612_);
lean_dec_ref_known(v___x_3611_, 1);
if (lean_obj_tag(v_val_3612_) == 2)
{
lean_object* v_n_3613_; lean_object* v_mantissa_3614_; lean_object* v_exponent_3615_; lean_object* v_natZero_3616_; lean_object* v_intZero_3617_; uint8_t v_isNeg_3618_; 
v_n_3613_ = lean_ctor_get(v_val_3612_, 0);
lean_inc_ref(v_n_3613_);
lean_dec_ref_known(v_val_3612_, 1);
v_mantissa_3614_ = lean_ctor_get(v_n_3613_, 0);
lean_inc(v_mantissa_3614_);
v_exponent_3615_ = lean_ctor_get(v_n_3613_, 1);
lean_inc(v_exponent_3615_);
lean_dec_ref(v_n_3613_);
v_natZero_3616_ = lean_unsigned_to_nat(0u);
v_intZero_3617_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3618_ = lean_int_dec_lt(v_mantissa_3614_, v_intZero_3617_);
if (v_isNeg_3618_ == 0)
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_nat_dec_eq(v_exponent_3615_, v_natZero_3616_);
lean_dec(v_exponent_3615_);
if (v___x_3619_ == 0)
{
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3585_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3620_);
if (lean_obj_tag(v___x_3621_) == 1)
{
lean_object* v_val_3622_; 
v_val_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v___x_3621_, 1);
if (lean_obj_tag(v_val_3622_) == 4)
{
lean_object* v_elems_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_elems_3623_ = lean_ctor_get(v_val_3622_, 0);
lean_inc_ref(v_elems_3623_);
lean_dec_ref_known(v_val_3622_, 1);
v___x_3624_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3624_);
if (lean_obj_tag(v___x_3625_) == 1)
{
lean_object* v_val_3626_; 
v_val_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_val_3626_);
lean_dec_ref_known(v___x_3625_, 1);
if (lean_obj_tag(v_val_3626_) == 2)
{
lean_object* v_n_3627_; lean_object* v_mantissa_3628_; lean_object* v_exponent_3629_; uint8_t v_isNeg_3630_; 
v_n_3627_ = lean_ctor_get(v_val_3626_, 0);
lean_inc_ref(v_n_3627_);
lean_dec_ref_known(v_val_3626_, 1);
v_mantissa_3628_ = lean_ctor_get(v_n_3627_, 0);
lean_inc(v_mantissa_3628_);
v_exponent_3629_ = lean_ctor_get(v_n_3627_, 1);
lean_inc(v_exponent_3629_);
lean_dec_ref(v_n_3627_);
v_isNeg_3630_ = lean_int_dec_lt(v_mantissa_3628_, v_intZero_3617_);
if (v_isNeg_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = lean_nat_dec_eq(v_exponent_3629_, v_natZero_3616_);
lean_dec(v_exponent_3629_);
if (v___x_3631_ == 0)
{
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3591_;
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2));
v___x_3633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3632_);
if (lean_obj_tag(v___x_3633_) == 1)
{
lean_object* v_val_3634_; 
v_val_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_val_3634_);
lean_dec_ref_known(v___x_3633_, 1);
if (lean_obj_tag(v_val_3634_) == 2)
{
lean_object* v_n_3635_; lean_object* v_mantissa_3636_; lean_object* v_exponent_3637_; uint8_t v_isNeg_3638_; 
v_n_3635_ = lean_ctor_get(v_val_3634_, 0);
lean_inc_ref(v_n_3635_);
lean_dec_ref_known(v_val_3634_, 1);
v_mantissa_3636_ = lean_ctor_get(v_n_3635_, 0);
lean_inc(v_mantissa_3636_);
v_exponent_3637_ = lean_ctor_get(v_n_3635_, 1);
lean_inc(v_exponent_3637_);
lean_dec_ref(v_n_3635_);
v_isNeg_3638_ = lean_int_dec_lt(v_mantissa_3636_, v_intZero_3617_);
if (v_isNeg_3638_ == 0)
{
uint8_t v___x_3639_; 
v___x_3639_ = lean_nat_dec_eq(v_exponent_3637_, v_natZero_3616_);
lean_dec(v_exponent_3637_);
if (v___x_3639_ == 0)
{
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3594_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3));
v___x_3641_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3640_);
if (lean_obj_tag(v___x_3641_) == 1)
{
lean_object* v_val_3642_; 
v_val_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v___x_3641_, 1);
if (lean_obj_tag(v_val_3642_) == 2)
{
lean_object* v_n_3643_; lean_object* v_mantissa_3644_; lean_object* v_exponent_3645_; uint8_t v_isNeg_3646_; 
v_n_3643_ = lean_ctor_get(v_val_3642_, 0);
lean_inc_ref(v_n_3643_);
lean_dec_ref_known(v_val_3642_, 1);
v_mantissa_3644_ = lean_ctor_get(v_n_3643_, 0);
lean_inc(v_mantissa_3644_);
v_exponent_3645_ = lean_ctor_get(v_n_3643_, 1);
lean_inc(v_exponent_3645_);
lean_dec_ref(v_n_3643_);
v_isNeg_3646_ = lean_int_dec_lt(v_mantissa_3644_, v_intZero_3617_);
if (v_isNeg_3646_ == 0)
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_nat_dec_eq(v_exponent_3645_, v_natZero_3616_);
lean_dec(v_exponent_3645_);
if (v___x_3647_ == 0)
{
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3597_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3648_);
if (lean_obj_tag(v___x_3649_) == 1)
{
lean_object* v_val_3650_; 
v_val_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_val_3650_);
lean_dec_ref_known(v___x_3649_, 1);
if (lean_obj_tag(v_val_3650_) == 2)
{
lean_object* v_n_3651_; lean_object* v_mantissa_3652_; lean_object* v_exponent_3653_; uint8_t v_isNeg_3654_; 
v_n_3651_ = lean_ctor_get(v_val_3650_, 0);
lean_inc_ref(v_n_3651_);
lean_dec_ref_known(v_val_3650_, 1);
v_mantissa_3652_ = lean_ctor_get(v_n_3651_, 0);
lean_inc(v_mantissa_3652_);
v_exponent_3653_ = lean_ctor_get(v_n_3651_, 1);
lean_inc(v_exponent_3653_);
lean_dec_ref(v_n_3651_);
v_isNeg_3654_ = lean_int_dec_lt(v_mantissa_3652_, v_intZero_3617_);
if (v_isNeg_3654_ == 0)
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_nat_dec_eq(v_exponent_3653_, v_natZero_3616_);
lean_dec(v_exponent_3653_);
if (v___x_3655_ == 0)
{
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3600_;
}
else
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4));
v___x_3657_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3656_);
if (lean_obj_tag(v___x_3657_) == 1)
{
lean_object* v_val_3658_; 
v_val_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v___x_3657_, 1);
if (lean_obj_tag(v_val_3658_) == 2)
{
lean_object* v_n_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3785_; 
v_n_3659_ = lean_ctor_get(v_val_3658_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_val_3658_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3661_ = v_val_3658_;
v_isShared_3662_ = v_isSharedCheck_3785_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_n_3659_);
lean_dec(v_val_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3785_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v_mantissa_3663_; lean_object* v_exponent_3664_; uint8_t v_isNeg_3665_; 
v_mantissa_3663_ = lean_ctor_get(v_n_3659_, 0);
lean_inc(v_mantissa_3663_);
v_exponent_3664_ = lean_ctor_get(v_n_3659_, 1);
lean_inc(v_exponent_3664_);
lean_dec_ref(v_n_3659_);
v_isNeg_3665_ = lean_int_dec_lt(v_mantissa_3663_, v_intZero_3617_);
if (v_isNeg_3665_ == 0)
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_nat_dec_eq(v_exponent_3664_, v_natZero_3616_);
lean_dec(v_exponent_3664_);
if (v___x_3666_ == 0)
{
lean_dec(v_mantissa_3663_);
lean_del_object(v___x_3661_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3603_;
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3609_, v___x_3667_);
if (lean_obj_tag(v___x_3668_) == 1)
{
lean_object* v_val_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3784_; 
v_val_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3784_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_val_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3784_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
if (lean_obj_tag(v_val_3669_) == 1)
{
uint8_t v_b_3673_; lean_object* v_nameMap_3674_; lean_object* v_a_3675_; lean_object* v___x_3676_; 
v_b_3673_ = lean_ctor_get_uint8(v_val_3669_, 0);
lean_dec_ref_known(v_val_3669_, 0);
v_nameMap_3674_ = lean_ctor_get(v_a_3583_, 1);
v_a_3675_ = lean_nat_abs(v_mantissa_3614_);
lean_dec(v_mantissa_3614_);
v___x_3676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3676_) == 1)
{
lean_object* v_val_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3675_);
lean_del_object(v___x_3671_);
lean_del_object(v___x_3661_);
v_val_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3774_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_val_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3774_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_a_3681_; lean_object* v_a_3682_; lean_object* v_a_3683_; lean_object* v_a_3684_; lean_object* v_a_3685_; lean_object* v___x_3686_; 
v_a_3681_ = lean_nat_abs(v_mantissa_3628_);
lean_dec(v_mantissa_3628_);
v_a_3682_ = lean_nat_abs(v_mantissa_3636_);
lean_dec(v_mantissa_3636_);
v_a_3683_ = lean_nat_abs(v_mantissa_3644_);
lean_dec(v_mantissa_3644_);
v_a_3684_ = lean_nat_abs(v_mantissa_3652_);
lean_dec(v_mantissa_3652_);
v_a_3685_ = lean_nat_abs(v_mantissa_3663_);
lean_dec(v_mantissa_3663_);
v___x_3686_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3623_, v_a_3583_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3765_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3765_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3765_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_snd_3691_; lean_object* v_fst_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3764_; 
v_snd_3691_ = lean_ctor_get(v_a_3687_, 1);
v_fst_3692_ = lean_ctor_get(v_a_3687_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3694_ = v_a_3687_;
v_isShared_3695_ = v_isSharedCheck_3764_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_snd_3691_);
lean_inc(v_fst_3692_);
lean_dec(v_a_3687_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3764_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_stream_3696_; lean_object* v_nameMap_3697_; lean_object* v_levelMap_3698_; lean_object* v_exprMap_3699_; lean_object* v_recursorRuleMap_3700_; lean_object* v_constMap_3701_; lean_object* v_constOrder_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3763_; 
v_stream_3696_ = lean_ctor_get(v_snd_3691_, 0);
v_nameMap_3697_ = lean_ctor_get(v_snd_3691_, 1);
v_levelMap_3698_ = lean_ctor_get(v_snd_3691_, 2);
v_exprMap_3699_ = lean_ctor_get(v_snd_3691_, 3);
v_recursorRuleMap_3700_ = lean_ctor_get(v_snd_3691_, 4);
v_constMap_3701_ = lean_ctor_get(v_snd_3691_, 5);
v_constOrder_3702_ = lean_ctor_get(v_snd_3691_, 6);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_snd_3691_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3704_ = v_snd_3691_;
v_isShared_3705_ = v_isSharedCheck_3763_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_constOrder_3702_);
lean_inc(v_constMap_3701_);
lean_inc(v_recursorRuleMap_3700_);
lean_inc(v_exprMap_3699_);
lean_inc(v_levelMap_3698_);
lean_inc(v_nameMap_3697_);
lean_inc(v_stream_3696_);
lean_dec(v_snd_3691_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3763_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3699_, v_a_3681_);
if (lean_obj_tag(v___x_3706_) == 1)
{
lean_object* v_val_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3681_);
lean_del_object(v___x_3679_);
v_val_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3753_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_val_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3753_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3697_, v_a_3682_);
if (lean_obj_tag(v___x_3711_) == 1)
{
lean_object* v_val_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3743_; 
lean_del_object(v___x_3709_);
lean_dec(v_a_3682_);
v_val_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3743_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_val_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3743_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3701_, v_val_3677_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_inc(v_val_3677_);
v___x_3717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3717_, 0, v_val_3677_);
lean_ctor_set(v___x_3717_, 1, v_fst_3692_);
lean_ctor_set(v___x_3717_, 2, v_val_3707_);
v___x_3718_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set(v___x_3718_, 1, v_val_3712_);
lean_ctor_set(v___x_3718_, 2, v_a_3683_);
lean_ctor_set(v___x_3718_, 3, v_a_3684_);
lean_ctor_set(v___x_3718_, 4, v_a_3685_);
lean_ctor_set_uint8(v___x_3718_, sizeof(void*)*5, v_b_3673_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 6);
lean_ctor_set(v___x_3714_, 0, v___x_3718_);
v___x_3720_ = v___x_3714_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3721_ = lean_box(0);
lean_inc(v_val_3677_);
v___x_3722_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3701_, v_val_3677_, v___x_3720_);
v___x_3723_ = lean_array_push(v_constOrder_3702_, v_val_3677_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 6, v___x_3723_);
lean_ctor_set(v___x_3704_, 5, v___x_3722_);
v___x_3725_ = v___x_3704_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_stream_3696_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_nameMap_3697_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_levelMap_3698_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_exprMap_3699_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_recursorRuleMap_3700_);
lean_ctor_set(v_reuseFailAlloc_3732_, 5, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3732_, 6, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3725_);
lean_ctor_set(v___x_3694_, 0, v___x_3721_);
v___x_3727_ = v___x_3694_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3727_);
v___x_3729_ = v___x_3689_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_dec(v_val_3712_);
lean_dec(v_val_3707_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_constOrder_3702_);
lean_dec_ref(v_constMap_3701_);
lean_dec_ref(v_recursorRuleMap_3700_);
lean_dec_ref(v_exprMap_3699_);
lean_dec_ref(v_levelMap_3698_);
lean_dec_ref(v_nameMap_3697_);
lean_dec_ref(v_stream_3696_);
lean_del_object(v___x_3694_);
lean_dec(v_fst_3692_);
lean_dec(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec(v_a_3683_);
v___x_3734_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3677_, v___x_3716_);
v___x_3736_ = lean_string_append(v___x_3734_, v___x_3735_);
lean_dec_ref(v___x_3735_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 18);
lean_ctor_set(v___x_3714_, 0, v___x_3736_);
v___x_3738_ = v___x_3714_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 1);
lean_ctor_set(v___x_3689_, 0, v___x_3738_);
v___x_3740_ = v___x_3689_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
lean_dec(v___x_3711_);
lean_dec(v_val_3707_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_constOrder_3702_);
lean_dec_ref(v_constMap_3701_);
lean_dec_ref(v_recursorRuleMap_3700_);
lean_dec_ref(v_exprMap_3699_);
lean_dec_ref(v_levelMap_3698_);
lean_dec_ref(v_nameMap_3697_);
lean_dec_ref(v_stream_3696_);
lean_del_object(v___x_3694_);
lean_dec(v_fst_3692_);
lean_dec(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec(v_val_3677_);
v___x_3744_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3745_ = l_Nat_reprFast(v_a_3682_);
v___x_3746_ = lean_string_append(v___x_3744_, v___x_3745_);
lean_dec_ref(v___x_3745_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set_tag(v___x_3709_, 18);
lean_ctor_set(v___x_3709_, 0, v___x_3746_);
v___x_3748_ = v___x_3709_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 1);
lean_ctor_set(v___x_3689_, 0, v___x_3748_);
v___x_3750_ = v___x_3689_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec(v___x_3706_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_constOrder_3702_);
lean_dec_ref(v_constMap_3701_);
lean_dec_ref(v_recursorRuleMap_3700_);
lean_dec_ref(v_exprMap_3699_);
lean_dec_ref(v_levelMap_3698_);
lean_dec_ref(v_nameMap_3697_);
lean_dec_ref(v_stream_3696_);
lean_del_object(v___x_3694_);
lean_dec(v_fst_3692_);
lean_dec(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec(v_val_3677_);
v___x_3754_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3755_ = l_Nat_reprFast(v_a_3681_);
v___x_3756_ = lean_string_append(v___x_3754_, v___x_3755_);
lean_dec_ref(v___x_3755_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 18);
lean_ctor_set(v___x_3679_, 0, v___x_3756_);
v___x_3758_ = v___x_3679_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 1);
lean_ctor_set(v___x_3689_, 0, v___x_3758_);
v___x_3760_ = v___x_3689_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec(v_a_3681_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
v_a_3766_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3686_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3686_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_dec(v___x_3676_);
lean_dec(v_mantissa_3663_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec_ref(v_a_3583_);
v___x_3775_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3776_ = l_Nat_reprFast(v_a_3675_);
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3776_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 18);
lean_ctor_set(v___x_3671_, 0, v___x_3777_);
v___x_3779_ = v___x_3671_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3781_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 1);
lean_ctor_set(v___x_3661_, 0, v___x_3779_);
v___x_3781_ = v___x_3661_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_del_object(v___x_3671_);
lean_dec(v_val_3669_);
lean_dec(v_mantissa_3663_);
lean_del_object(v___x_3661_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3606_;
}
}
}
else
{
lean_dec(v___x_3668_);
lean_dec(v_mantissa_3663_);
lean_del_object(v___x_3661_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3606_;
}
}
}
else
{
lean_dec(v_exponent_3664_);
lean_dec(v_mantissa_3663_);
lean_del_object(v___x_3661_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3603_;
}
}
}
else
{
lean_dec(v_val_3658_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3603_;
}
}
else
{
lean_dec(v___x_3657_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3603_;
}
}
}
else
{
lean_dec(v_exponent_3653_);
lean_dec(v_mantissa_3652_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3600_;
}
}
else
{
lean_dec(v_val_3650_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3600_;
}
}
else
{
lean_dec(v___x_3649_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3600_;
}
}
}
else
{
lean_dec(v_exponent_3645_);
lean_dec(v_mantissa_3644_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3597_;
}
}
else
{
lean_dec(v_val_3642_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3597_;
}
}
else
{
lean_dec(v___x_3641_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3597_;
}
}
}
else
{
lean_dec(v_exponent_3637_);
lean_dec(v_mantissa_3636_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3594_;
}
}
else
{
lean_dec(v_val_3634_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3594_;
}
}
else
{
lean_dec(v___x_3633_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3594_;
}
}
}
else
{
lean_dec(v_exponent_3629_);
lean_dec(v_mantissa_3628_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3591_;
}
}
else
{
lean_dec(v_val_3626_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3591_;
}
}
else
{
lean_dec(v___x_3625_);
lean_dec_ref(v_elems_3623_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3591_;
}
}
else
{
lean_dec(v_val_3622_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3588_;
}
}
else
{
lean_dec(v___x_3621_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3588_;
}
}
}
else
{
lean_dec(v_exponent_3615_);
lean_dec(v_mantissa_3614_);
lean_dec_ref(v_a_3583_);
goto v___jp_3585_;
}
}
else
{
lean_dec(v_val_3612_);
lean_dec_ref(v_a_3583_);
goto v___jp_3585_;
}
}
else
{
lean_dec(v___x_3611_);
lean_dec_ref(v_a_3583_);
goto v___jp_3585_;
}
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec_ref(v_a_3583_);
v___x_3786_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
v___jp_3585_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
v___jp_3588_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
v___jp_3591_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
v___jp_3594_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
v___jp_3597_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
v___jp_3600_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
return v___x_3602_;
}
v___jp_3603_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
return v___x_3605_;
}
v___jp_3606_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___boxed(lean_object* v_json_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v_json_3788_, v_a_3789_);
lean_dec(v_json_3788_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(lean_object* v_x_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_){
_start:
{
if (lean_obj_tag(v_x_3797_) == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = l_List_reverse___redArg(v_x_3798_);
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
lean_ctor_set(v___x_3811_, 1, v___y_3799_);
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
else
{
lean_object* v_head_3813_; 
v_head_3813_ = lean_ctor_get(v_x_3797_, 0);
lean_inc(v_head_3813_);
if (lean_obj_tag(v_head_3813_) == 5)
{
lean_object* v_tail_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3889_; 
v_tail_3814_ = lean_ctor_get(v_x_3797_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_x_3797_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_x_3797_, 0);
lean_dec(v_unused_3890_);
v___x_3816_ = v_x_3797_;
v_isShared_3817_ = v_isSharedCheck_3889_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_tail_3814_);
lean_dec(v_x_3797_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3889_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v_kvPairs_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_kvPairs_3818_ = lean_ctor_get(v_head_3813_, 0);
lean_inc(v_kvPairs_3818_);
lean_dec_ref_known(v_head_3813_, 1);
v___x_3819_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3820_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3818_, v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 1)
{
lean_object* v_val_3821_; 
v_val_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_val_3821_);
lean_dec_ref_known(v___x_3820_, 1);
if (lean_obj_tag(v_val_3821_) == 2)
{
lean_object* v_n_3822_; lean_object* v_mantissa_3823_; lean_object* v_exponent_3824_; lean_object* v_natZero_3825_; lean_object* v_intZero_3826_; uint8_t v_isNeg_3827_; 
v_n_3822_ = lean_ctor_get(v_val_3821_, 0);
lean_inc_ref(v_n_3822_);
lean_dec_ref_known(v_val_3821_, 1);
v_mantissa_3823_ = lean_ctor_get(v_n_3822_, 0);
lean_inc(v_mantissa_3823_);
v_exponent_3824_ = lean_ctor_get(v_n_3822_, 1);
lean_inc(v_exponent_3824_);
lean_dec_ref(v_n_3822_);
v_natZero_3825_ = lean_unsigned_to_nat(0u);
v_intZero_3826_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3827_ = lean_int_dec_lt(v_mantissa_3823_, v_intZero_3826_);
if (v_isNeg_3827_ == 0)
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_eq(v_exponent_3824_, v_natZero_3825_);
lean_dec(v_exponent_3824_);
if (v___x_3828_ == 0)
{
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3801_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2));
v___x_3830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3818_, v___x_3829_);
if (lean_obj_tag(v___x_3830_) == 1)
{
lean_object* v_val_3831_; 
v_val_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_val_3831_);
lean_dec_ref_known(v___x_3830_, 1);
if (lean_obj_tag(v_val_3831_) == 2)
{
lean_object* v_n_3832_; lean_object* v_mantissa_3833_; lean_object* v_exponent_3834_; uint8_t v_isNeg_3835_; 
v_n_3832_ = lean_ctor_get(v_val_3831_, 0);
lean_inc_ref(v_n_3832_);
lean_dec_ref_known(v_val_3831_, 1);
v_mantissa_3833_ = lean_ctor_get(v_n_3832_, 0);
lean_inc(v_mantissa_3833_);
v_exponent_3834_ = lean_ctor_get(v_n_3832_, 1);
lean_inc(v_exponent_3834_);
lean_dec_ref(v_n_3832_);
v_isNeg_3835_ = lean_int_dec_lt(v_mantissa_3833_, v_intZero_3826_);
if (v_isNeg_3835_ == 0)
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_nat_dec_eq(v_exponent_3834_, v_natZero_3825_);
lean_dec(v_exponent_3834_);
if (v___x_3836_ == 0)
{
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3804_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3));
v___x_3838_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3818_, v___x_3837_);
lean_dec(v_kvPairs_3818_);
if (lean_obj_tag(v___x_3838_) == 1)
{
lean_object* v_val_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3888_; 
v_val_3839_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3841_ = v___x_3838_;
v_isShared_3842_ = v_isSharedCheck_3888_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_val_3839_);
lean_dec(v___x_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3888_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
if (lean_obj_tag(v_val_3839_) == 2)
{
lean_object* v_n_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3887_; 
v_n_3843_ = lean_ctor_get(v_val_3839_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_val_3839_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3845_ = v_val_3839_;
v_isShared_3846_ = v_isSharedCheck_3887_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_n_3843_);
lean_dec(v_val_3839_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3887_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_mantissa_3847_; lean_object* v_exponent_3848_; uint8_t v_isNeg_3849_; 
v_mantissa_3847_ = lean_ctor_get(v_n_3843_, 0);
lean_inc(v_mantissa_3847_);
v_exponent_3848_ = lean_ctor_get(v_n_3843_, 1);
lean_inc(v_exponent_3848_);
lean_dec_ref(v_n_3843_);
v_isNeg_3849_ = lean_int_dec_lt(v_mantissa_3847_, v_intZero_3826_);
if (v_isNeg_3849_ == 0)
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_nat_dec_eq(v_exponent_3848_, v_natZero_3825_);
lean_dec(v_exponent_3848_);
if (v___x_3850_ == 0)
{
lean_dec(v_mantissa_3847_);
lean_del_object(v___x_3845_);
lean_del_object(v___x_3841_);
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3807_;
}
else
{
lean_object* v_nameMap_3851_; lean_object* v_exprMap_3852_; lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_nameMap_3851_ = lean_ctor_get(v___y_3799_, 1);
v_exprMap_3852_ = lean_ctor_get(v___y_3799_, 3);
v_a_3853_ = lean_nat_abs(v_mantissa_3823_);
lean_dec(v_mantissa_3823_);
v___x_3854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3851_, v_a_3853_);
if (lean_obj_tag(v___x_3854_) == 1)
{
lean_object* v_val_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3853_);
lean_del_object(v___x_3841_);
v_val_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3877_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_val_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3877_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_a_3859_; lean_object* v___x_3860_; 
v_a_3859_ = lean_nat_abs(v_mantissa_3847_);
lean_dec(v_mantissa_3847_);
v___x_3860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3852_, v_a_3859_);
if (lean_obj_tag(v___x_3860_) == 1)
{
lean_object* v_val_3861_; lean_object* v_a_3862_; lean_object* v___x_3863_; lean_object* v___x_3865_; 
lean_dec(v_a_3859_);
lean_del_object(v___x_3857_);
lean_del_object(v___x_3845_);
v_val_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_val_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v_a_3862_ = lean_nat_abs(v_mantissa_3833_);
lean_dec(v_mantissa_3833_);
v___x_3863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3863_, 0, v_val_3855_);
lean_ctor_set(v___x_3863_, 1, v_a_3862_);
lean_ctor_set(v___x_3863_, 2, v_val_3861_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 1, v_x_3798_);
lean_ctor_set(v___x_3816_, 0, v___x_3863_);
v___x_3865_ = v___x_3816_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_x_3798_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
v_x_3797_ = v_tail_3814_;
v_x_3798_ = v___x_3865_;
goto _start;
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v___x_3860_);
lean_dec(v_val_3855_);
lean_dec(v_mantissa_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
v___x_3868_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3869_ = l_Nat_reprFast(v_a_3859_);
v___x_3870_ = lean_string_append(v___x_3868_, v___x_3869_);
lean_dec_ref(v___x_3869_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set_tag(v___x_3857_, 18);
lean_ctor_set(v___x_3857_, 0, v___x_3870_);
v___x_3872_ = v___x_3857_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 1);
lean_ctor_set(v___x_3845_, 0, v___x_3872_);
v___x_3874_ = v___x_3845_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
lean_dec(v___x_3854_);
lean_dec(v_mantissa_3847_);
lean_dec(v_mantissa_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
v___x_3878_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3879_ = l_Nat_reprFast(v_a_3853_);
v___x_3880_ = lean_string_append(v___x_3878_, v___x_3879_);
lean_dec_ref(v___x_3879_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 18);
lean_ctor_set(v___x_3845_, 0, v___x_3880_);
v___x_3882_ = v___x_3845_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3882_);
v___x_3884_ = v___x_3841_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
else
{
lean_dec(v_exponent_3848_);
lean_dec(v_mantissa_3847_);
lean_del_object(v___x_3845_);
lean_del_object(v___x_3841_);
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3807_;
}
}
}
else
{
lean_del_object(v___x_3841_);
lean_dec(v_val_3839_);
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3807_;
}
}
}
else
{
lean_dec(v___x_3838_);
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3807_;
}
}
}
else
{
lean_dec(v_exponent_3834_);
lean_dec(v_mantissa_3833_);
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3804_;
}
}
else
{
lean_dec(v_val_3831_);
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3804_;
}
}
else
{
lean_dec(v___x_3830_);
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3804_;
}
}
}
else
{
lean_dec(v_exponent_3824_);
lean_dec(v_mantissa_3823_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3801_;
}
}
else
{
lean_dec(v_val_3821_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3801_;
}
}
else
{
lean_dec(v___x_3820_);
lean_dec(v_kvPairs_3818_);
lean_del_object(v___x_3816_);
lean_dec(v_tail_3814_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
goto v___jp_3801_;
}
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
lean_dec_ref_known(v_x_3797_, 2);
lean_dec(v_head_3813_);
lean_dec_ref(v___y_3799_);
lean_dec(v_x_3798_);
v___x_3891_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
return v___x_3892_;
}
}
v___jp_3801_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
v___jp_3804_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
v___jp_3807_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___boxed(lean_object* v_x_3893_, lean_object* v_x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v_x_3893_, v_x_3894_, v___y_3895_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(lean_object* v_json_3902_, lean_object* v_a_3903_){
_start:
{
if (lean_obj_tag(v_json_3902_) == 5)
{
lean_object* v_kvPairs_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_kvPairs_3938_ = lean_ctor_get(v_json_3902_, 0);
v___x_3939_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3940_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3939_);
if (lean_obj_tag(v___x_3940_) == 1)
{
lean_object* v_val_3941_; 
v_val_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_val_3941_);
lean_dec_ref_known(v___x_3940_, 1);
if (lean_obj_tag(v_val_3941_) == 2)
{
lean_object* v_n_3942_; lean_object* v_mantissa_3943_; lean_object* v_exponent_3944_; lean_object* v_natZero_3945_; lean_object* v_intZero_3946_; uint8_t v_isNeg_3947_; 
v_n_3942_ = lean_ctor_get(v_val_3941_, 0);
lean_inc_ref(v_n_3942_);
lean_dec_ref_known(v_val_3941_, 1);
v_mantissa_3943_ = lean_ctor_get(v_n_3942_, 0);
lean_inc(v_mantissa_3943_);
v_exponent_3944_ = lean_ctor_get(v_n_3942_, 1);
lean_inc(v_exponent_3944_);
lean_dec_ref(v_n_3942_);
v_natZero_3945_ = lean_unsigned_to_nat(0u);
v_intZero_3946_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3947_ = lean_int_dec_lt(v_mantissa_3943_, v_intZero_3946_);
if (v_isNeg_3947_ == 0)
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_nat_dec_eq(v_exponent_3944_, v_natZero_3945_);
lean_dec(v_exponent_3944_);
if (v___x_3948_ == 0)
{
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3905_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3949_);
if (lean_obj_tag(v___x_3950_) == 1)
{
lean_object* v_val_3951_; 
v_val_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v___x_3950_, 1);
if (lean_obj_tag(v_val_3951_) == 4)
{
lean_object* v_elems_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_elems_3952_ = lean_ctor_get(v_val_3951_, 0);
lean_inc_ref(v_elems_3952_);
lean_dec_ref_known(v_val_3951_, 1);
v___x_3953_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3953_);
if (lean_obj_tag(v___x_3954_) == 1)
{
lean_object* v_val_3955_; 
v_val_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_val_3955_);
lean_dec_ref_known(v___x_3954_, 1);
if (lean_obj_tag(v_val_3955_) == 2)
{
lean_object* v_n_3956_; lean_object* v_mantissa_3957_; lean_object* v_exponent_3958_; uint8_t v_isNeg_3959_; 
v_n_3956_ = lean_ctor_get(v_val_3955_, 0);
lean_inc_ref(v_n_3956_);
lean_dec_ref_known(v_val_3955_, 1);
v_mantissa_3957_ = lean_ctor_get(v_n_3956_, 0);
lean_inc(v_mantissa_3957_);
v_exponent_3958_ = lean_ctor_get(v_n_3956_, 1);
lean_inc(v_exponent_3958_);
lean_dec_ref(v_n_3956_);
v_isNeg_3959_ = lean_int_dec_lt(v_mantissa_3957_, v_intZero_3946_);
if (v_isNeg_3959_ == 0)
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_nat_dec_eq(v_exponent_3958_, v_natZero_3945_);
lean_dec(v_exponent_3958_);
if (v___x_3960_ == 0)
{
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3911_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3962_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3961_);
if (lean_obj_tag(v___x_3962_) == 1)
{
lean_object* v_val_3963_; 
v_val_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_val_3963_);
lean_dec_ref_known(v___x_3962_, 1);
if (lean_obj_tag(v_val_3963_) == 4)
{
lean_object* v_elems_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_elems_3964_ = lean_ctor_get(v_val_3963_, 0);
lean_inc_ref(v_elems_3964_);
lean_dec_ref_known(v_val_3963_, 1);
v___x_3965_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3966_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3965_);
if (lean_obj_tag(v___x_3966_) == 1)
{
lean_object* v_val_3967_; 
v_val_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_val_3967_);
lean_dec_ref_known(v___x_3966_, 1);
if (lean_obj_tag(v_val_3967_) == 2)
{
lean_object* v_n_3968_; lean_object* v_mantissa_3969_; lean_object* v_exponent_3970_; uint8_t v_isNeg_3971_; 
v_n_3968_ = lean_ctor_get(v_val_3967_, 0);
lean_inc_ref(v_n_3968_);
lean_dec_ref_known(v_val_3967_, 1);
v_mantissa_3969_ = lean_ctor_get(v_n_3968_, 0);
lean_inc(v_mantissa_3969_);
v_exponent_3970_ = lean_ctor_get(v_n_3968_, 1);
lean_inc(v_exponent_3970_);
lean_dec_ref(v_n_3968_);
v_isNeg_3971_ = lean_int_dec_lt(v_mantissa_3969_, v_intZero_3946_);
if (v_isNeg_3971_ == 0)
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_eq(v_exponent_3970_, v_natZero_3945_);
lean_dec(v_exponent_3970_);
if (v___x_3972_ == 0)
{
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3917_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3974_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3973_);
if (lean_obj_tag(v___x_3974_) == 1)
{
lean_object* v_val_3975_; 
v_val_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_val_3975_);
lean_dec_ref_known(v___x_3974_, 1);
if (lean_obj_tag(v_val_3975_) == 2)
{
lean_object* v_n_3976_; lean_object* v_mantissa_3977_; lean_object* v_exponent_3978_; uint8_t v_isNeg_3979_; 
v_n_3976_ = lean_ctor_get(v_val_3975_, 0);
lean_inc_ref(v_n_3976_);
lean_dec_ref_known(v_val_3975_, 1);
v_mantissa_3977_ = lean_ctor_get(v_n_3976_, 0);
lean_inc(v_mantissa_3977_);
v_exponent_3978_ = lean_ctor_get(v_n_3976_, 1);
lean_inc(v_exponent_3978_);
lean_dec_ref(v_n_3976_);
v_isNeg_3979_ = lean_int_dec_lt(v_mantissa_3977_, v_intZero_3946_);
if (v_isNeg_3979_ == 0)
{
uint8_t v___x_3980_; 
v___x_3980_ = lean_nat_dec_eq(v_exponent_3978_, v_natZero_3945_);
lean_dec(v_exponent_3978_);
if (v___x_3980_ == 0)
{
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3920_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0));
v___x_3982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3981_);
if (lean_obj_tag(v___x_3982_) == 1)
{
lean_object* v_val_3983_; 
v_val_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v___x_3982_, 1);
if (lean_obj_tag(v_val_3983_) == 2)
{
lean_object* v_n_3984_; lean_object* v_mantissa_3985_; lean_object* v_exponent_3986_; uint8_t v_isNeg_3987_; 
v_n_3984_ = lean_ctor_get(v_val_3983_, 0);
lean_inc_ref(v_n_3984_);
lean_dec_ref_known(v_val_3983_, 1);
v_mantissa_3985_ = lean_ctor_get(v_n_3984_, 0);
lean_inc(v_mantissa_3985_);
v_exponent_3986_ = lean_ctor_get(v_n_3984_, 1);
lean_inc(v_exponent_3986_);
lean_dec_ref(v_n_3984_);
v_isNeg_3987_ = lean_int_dec_lt(v_mantissa_3985_, v_intZero_3946_);
if (v_isNeg_3987_ == 0)
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_eq(v_exponent_3986_, v_natZero_3945_);
lean_dec(v_exponent_3986_);
if (v___x_3988_ == 0)
{
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3923_;
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1));
v___x_3990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3989_);
if (lean_obj_tag(v___x_3990_) == 1)
{
lean_object* v_val_3991_; 
v_val_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_val_3991_);
lean_dec_ref_known(v___x_3990_, 1);
if (lean_obj_tag(v_val_3991_) == 2)
{
lean_object* v_n_3992_; lean_object* v_mantissa_3993_; lean_object* v_exponent_3994_; uint8_t v_isNeg_3995_; 
v_n_3992_ = lean_ctor_get(v_val_3991_, 0);
lean_inc_ref(v_n_3992_);
lean_dec_ref_known(v_val_3991_, 1);
v_mantissa_3993_ = lean_ctor_get(v_n_3992_, 0);
lean_inc(v_mantissa_3993_);
v_exponent_3994_ = lean_ctor_get(v_n_3992_, 1);
lean_inc(v_exponent_3994_);
lean_dec_ref(v_n_3992_);
v_isNeg_3995_ = lean_int_dec_lt(v_mantissa_3993_, v_intZero_3946_);
if (v_isNeg_3995_ == 0)
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_nat_dec_eq(v_exponent_3994_, v_natZero_3945_);
lean_dec(v_exponent_3994_);
if (v___x_3996_ == 0)
{
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3926_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2));
v___x_3998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_3997_);
if (lean_obj_tag(v___x_3998_) == 1)
{
lean_object* v_val_3999_; 
v_val_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v___x_3998_, 1);
if (lean_obj_tag(v_val_3999_) == 1)
{
uint8_t v_b_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_b_4000_ = lean_ctor_get_uint8(v_val_3999_, 0);
lean_dec_ref_known(v_val_3999_, 0);
v___x_4001_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3));
v___x_4002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_4001_);
if (lean_obj_tag(v___x_4002_) == 1)
{
lean_object* v_val_4003_; 
v_val_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v___x_4002_, 1);
if (lean_obj_tag(v_val_4003_) == 4)
{
lean_object* v_elems_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4142_; 
v_elems_4004_ = lean_ctor_get(v_val_4003_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_val_4003_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4006_ = v_val_4003_;
v_isShared_4007_ = v_isSharedCheck_4142_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_elems_4004_);
lean_dec(v_val_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4142_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_4009_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3938_, v___x_4008_);
if (lean_obj_tag(v___x_4009_) == 1)
{
lean_object* v_val_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4141_; 
v_val_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4141_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_val_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4141_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
if (lean_obj_tag(v_val_4010_) == 1)
{
uint8_t v_b_4014_; lean_object* v_nameMap_4015_; lean_object* v_a_4016_; lean_object* v___x_4017_; 
v_b_4014_ = lean_ctor_get_uint8(v_val_4010_, 0);
lean_dec_ref_known(v_val_4010_, 0);
v_nameMap_4015_ = lean_ctor_get(v_a_3903_, 1);
v_a_4016_ = lean_nat_abs(v_mantissa_3943_);
lean_dec(v_mantissa_3943_);
v___x_4017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4017_) == 1)
{
lean_object* v_val_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v_a_4016_);
lean_del_object(v___x_4012_);
lean_del_object(v___x_4006_);
v_val_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4131_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_val_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4131_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v_a_4022_; lean_object* v_a_4023_; lean_object* v_a_4024_; lean_object* v_a_4025_; lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4022_ = lean_nat_abs(v_mantissa_3957_);
lean_dec(v_mantissa_3957_);
v_a_4023_ = lean_nat_abs(v_mantissa_3969_);
lean_dec(v_mantissa_3969_);
v_a_4024_ = lean_nat_abs(v_mantissa_3977_);
lean_dec(v_mantissa_3977_);
v_a_4025_ = lean_nat_abs(v_mantissa_3985_);
lean_dec(v_mantissa_3985_);
v_a_4026_ = lean_nat_abs(v_mantissa_3993_);
lean_dec(v_mantissa_3993_);
v___x_4027_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3952_, v_a_3903_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4122_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4122_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4122_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_snd_4032_; lean_object* v_fst_4033_; lean_object* v_exprMap_4034_; lean_object* v___x_4035_; 
v_snd_4032_ = lean_ctor_get(v_a_4028_, 1);
lean_inc(v_snd_4032_);
v_fst_4033_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_fst_4033_);
lean_dec(v_a_4028_);
v_exprMap_4034_ = lean_ctor_get(v_snd_4032_, 3);
v___x_4035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_4034_, v_a_4022_);
if (lean_obj_tag(v___x_4035_) == 1)
{
lean_object* v_val_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4112_; 
lean_del_object(v___x_4030_);
lean_dec(v_a_4022_);
lean_del_object(v___x_4020_);
v_val_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4112_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_val_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4112_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; 
v___x_4040_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3964_, v_snd_4032_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v_fst_4042_; lean_object* v_snd_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v_fst_4042_ = lean_ctor_get(v_a_4041_, 0);
lean_inc(v_fst_4042_);
v_snd_4043_ = lean_ctor_get(v_a_4041_, 1);
lean_inc(v_snd_4043_);
lean_dec(v_a_4041_);
v___x_4044_ = lean_array_to_list(v_elems_4004_);
v___x_4045_ = lean_box(0);
v___x_4046_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v___x_4044_, v___x_4045_, v_snd_4043_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4095_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4095_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4095_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_snd_4051_; lean_object* v_fst_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4094_; 
v_snd_4051_ = lean_ctor_get(v_a_4047_, 1);
v_fst_4052_ = lean_ctor_get(v_a_4047_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_a_4047_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4054_ = v_a_4047_;
v_isShared_4055_ = v_isSharedCheck_4094_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_snd_4051_);
lean_inc(v_fst_4052_);
lean_dec(v_a_4047_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4094_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_stream_4056_; lean_object* v_nameMap_4057_; lean_object* v_levelMap_4058_; lean_object* v_exprMap_4059_; lean_object* v_recursorRuleMap_4060_; lean_object* v_constMap_4061_; lean_object* v_constOrder_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4093_; 
v_stream_4056_ = lean_ctor_get(v_snd_4051_, 0);
v_nameMap_4057_ = lean_ctor_get(v_snd_4051_, 1);
v_levelMap_4058_ = lean_ctor_get(v_snd_4051_, 2);
v_exprMap_4059_ = lean_ctor_get(v_snd_4051_, 3);
v_recursorRuleMap_4060_ = lean_ctor_get(v_snd_4051_, 4);
v_constMap_4061_ = lean_ctor_get(v_snd_4051_, 5);
v_constOrder_4062_ = lean_ctor_get(v_snd_4051_, 6);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_snd_4051_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4064_ = v_snd_4051_;
v_isShared_4065_ = v_isSharedCheck_4093_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_constOrder_4062_);
lean_inc(v_constMap_4061_);
lean_inc(v_recursorRuleMap_4060_);
lean_inc(v_exprMap_4059_);
lean_inc(v_levelMap_4058_);
lean_inc(v_nameMap_4057_);
lean_inc(v_stream_4056_);
lean_dec(v_snd_4051_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4093_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
uint8_t v___x_4066_; 
v___x_4066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_4061_, v_val_4018_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_inc(v_val_4018_);
v___x_4067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4067_, 0, v_val_4018_);
lean_ctor_set(v___x_4067_, 1, v_fst_4033_);
lean_ctor_set(v___x_4067_, 2, v_val_4036_);
v___x_4068_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
lean_ctor_set(v___x_4068_, 1, v_fst_4042_);
lean_ctor_set(v___x_4068_, 2, v_a_4023_);
lean_ctor_set(v___x_4068_, 3, v_a_4024_);
lean_ctor_set(v___x_4068_, 4, v_a_4025_);
lean_ctor_set(v___x_4068_, 5, v_a_4026_);
lean_ctor_set(v___x_4068_, 6, v_fst_4052_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7, v_b_4000_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 1, v_b_4014_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 7);
lean_ctor_set(v___x_4038_, 0, v___x_4068_);
v___x_4070_ = v___x_4038_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4071_ = lean_box(0);
lean_inc(v_val_4018_);
v___x_4072_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_4061_, v_val_4018_, v___x_4070_);
v___x_4073_ = lean_array_push(v_constOrder_4062_, v_val_4018_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 6, v___x_4073_);
lean_ctor_set(v___x_4064_, 5, v___x_4072_);
v___x_4075_ = v___x_4064_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_stream_4056_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_nameMap_4057_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_levelMap_4058_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_exprMap_4059_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_recursorRuleMap_4060_);
lean_ctor_set(v_reuseFailAlloc_4082_, 5, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4082_, 6, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4077_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v___x_4075_);
lean_ctor_set(v___x_4054_, 0, v___x_4071_);
v___x_4077_ = v___x_4054_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4079_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4077_);
v___x_4079_ = v___x_4049_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
lean_del_object(v___x_4064_);
lean_dec_ref(v_constOrder_4062_);
lean_dec_ref(v_constMap_4061_);
lean_dec_ref(v_recursorRuleMap_4060_);
lean_dec_ref(v_exprMap_4059_);
lean_dec_ref(v_levelMap_4058_);
lean_dec_ref(v_nameMap_4057_);
lean_dec_ref(v_stream_4056_);
lean_del_object(v___x_4054_);
lean_dec(v_fst_4052_);
lean_dec(v_fst_4042_);
lean_dec(v_val_4036_);
lean_dec(v_fst_4033_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
v___x_4084_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_4085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_4018_, v___x_4066_);
v___x_4086_ = lean_string_append(v___x_4084_, v___x_4085_);
lean_dec_ref(v___x_4085_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 18);
lean_ctor_set(v___x_4038_, 0, v___x_4086_);
v___x_4088_ = v___x_4038_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set_tag(v___x_4049_, 1);
lean_ctor_set(v___x_4049_, 0, v___x_4088_);
v___x_4090_ = v___x_4049_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_fst_4042_);
lean_del_object(v___x_4038_);
lean_dec(v_val_4036_);
lean_dec(v_fst_4033_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec(v_val_4018_);
v_a_4096_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4046_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4046_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_del_object(v___x_4038_);
lean_dec(v_val_4036_);
lean_dec(v_fst_4033_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec(v_val_4018_);
lean_dec_ref(v_elems_4004_);
v_a_4104_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4040_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4040_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
lean_dec(v___x_4035_);
lean_dec(v_fst_4033_);
lean_dec(v_snd_4032_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec(v_val_4018_);
lean_dec_ref(v_elems_4004_);
lean_dec_ref(v_elems_3964_);
v___x_4113_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_4114_ = l_Nat_reprFast(v_a_4022_);
v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
lean_dec_ref(v___x_4114_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set_tag(v___x_4020_, 18);
lean_ctor_set(v___x_4020_, 0, v___x_4115_);
v___x_4117_ = v___x_4020_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4119_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set_tag(v___x_4030_, 1);
lean_ctor_set(v___x_4030_, 0, v___x_4117_);
v___x_4119_ = v___x_4030_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec(v_a_4022_);
lean_del_object(v___x_4020_);
lean_dec(v_val_4018_);
lean_dec_ref(v_elems_4004_);
lean_dec_ref(v_elems_3964_);
v_a_4123_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4027_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4027_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
lean_dec(v___x_4017_);
lean_dec_ref(v_elems_4004_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec_ref(v_a_3903_);
v___x_4132_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_4133_ = l_Nat_reprFast(v_a_4016_);
v___x_4134_ = lean_string_append(v___x_4132_, v___x_4133_);
lean_dec_ref(v___x_4133_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 18);
lean_ctor_set(v___x_4012_, 0, v___x_4134_);
v___x_4136_ = v___x_4012_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4138_; 
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 1);
lean_ctor_set(v___x_4006_, 0, v___x_4136_);
v___x_4138_ = v___x_4006_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
else
{
lean_del_object(v___x_4012_);
lean_dec(v_val_4010_);
lean_del_object(v___x_4006_);
lean_dec_ref(v_elems_4004_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3935_;
}
}
}
else
{
lean_dec(v___x_4009_);
lean_del_object(v___x_4006_);
lean_dec_ref(v_elems_4004_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3935_;
}
}
}
else
{
lean_dec(v_val_4003_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3932_;
}
}
else
{
lean_dec(v___x_4002_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3932_;
}
}
else
{
lean_dec(v_val_3999_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3929_;
}
}
else
{
lean_dec(v___x_3998_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3929_;
}
}
}
else
{
lean_dec(v_exponent_3994_);
lean_dec(v_mantissa_3993_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3926_;
}
}
else
{
lean_dec(v_val_3991_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3926_;
}
}
else
{
lean_dec(v___x_3990_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3926_;
}
}
}
else
{
lean_dec(v_exponent_3986_);
lean_dec(v_mantissa_3985_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3923_;
}
}
else
{
lean_dec(v_val_3983_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3923_;
}
}
else
{
lean_dec(v___x_3982_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3923_;
}
}
}
else
{
lean_dec(v_exponent_3978_);
lean_dec(v_mantissa_3977_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3920_;
}
}
else
{
lean_dec(v_val_3975_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3920_;
}
}
else
{
lean_dec(v___x_3974_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3920_;
}
}
}
else
{
lean_dec(v_exponent_3970_);
lean_dec(v_mantissa_3969_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3917_;
}
}
else
{
lean_dec(v_val_3967_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3917_;
}
}
else
{
lean_dec(v___x_3966_);
lean_dec_ref(v_elems_3964_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3917_;
}
}
else
{
lean_dec(v_val_3963_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3914_;
}
}
else
{
lean_dec(v___x_3962_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3914_;
}
}
}
else
{
lean_dec(v_exponent_3958_);
lean_dec(v_mantissa_3957_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3911_;
}
}
else
{
lean_dec(v_val_3955_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3911_;
}
}
else
{
lean_dec(v___x_3954_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3911_;
}
}
else
{
lean_dec(v_val_3951_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3908_;
}
}
else
{
lean_dec(v___x_3950_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3908_;
}
}
}
else
{
lean_dec(v_exponent_3944_);
lean_dec(v_mantissa_3943_);
lean_dec_ref(v_a_3903_);
goto v___jp_3905_;
}
}
else
{
lean_dec(v_val_3941_);
lean_dec_ref(v_a_3903_);
goto v___jp_3905_;
}
}
else
{
lean_dec(v___x_3940_);
lean_dec_ref(v_a_3903_);
goto v___jp_3905_;
}
}
else
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref(v_a_3903_);
v___x_4143_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
v___jp_3905_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
return v___x_3907_;
}
v___jp_3908_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
v___jp_3911_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
v___jp_3914_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
v___jp_3917_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
return v___x_3919_;
}
v___jp_3920_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
v___jp_3923_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
v___jp_3926_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
v___jp_3929_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
v___jp_3932_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
v___jp_3935_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___boxed(lean_object* v_json_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v_json_4145_, v_a_4146_);
lean_dec(v_json_4145_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(lean_object* v_as_4149_, size_t v_i_4150_, size_t v_stop_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_){
_start:
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_usize_dec_eq(v_i_4150_, v_stop_4151_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_array_uget_borrowed(v_as_4149_, v_i_4150_);
v___x_4157_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v___x_4156_, v___y_4153_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v_fst_4159_; lean_object* v_snd_4160_; size_t v___x_4161_; size_t v___x_4162_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v_fst_4159_ = lean_ctor_get(v_a_4158_, 0);
lean_inc(v_fst_4159_);
v_snd_4160_ = lean_ctor_get(v_a_4158_, 1);
lean_inc(v_snd_4160_);
lean_dec(v_a_4158_);
v___x_4161_ = ((size_t)1ULL);
v___x_4162_ = lean_usize_add(v_i_4150_, v___x_4161_);
v_i_4150_ = v___x_4162_;
v_b_4152_ = v_fst_4159_;
v___y_4153_ = v_snd_4160_;
goto _start;
}
else
{
return v___x_4157_;
}
}
else
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v_b_4152_);
lean_ctor_set(v___x_4164_, 1, v___y_4153_);
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
return v___x_4165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0___boxed(lean_object* v_as_4166_, lean_object* v_i_4167_, lean_object* v_stop_4168_, lean_object* v_b_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
size_t v_i_boxed_4172_; size_t v_stop_boxed_4173_; lean_object* v_res_4174_; 
v_i_boxed_4172_ = lean_unbox_usize(v_i_4167_);
lean_dec(v_i_4167_);
v_stop_boxed_4173_ = lean_unbox_usize(v_stop_4168_);
lean_dec(v_stop_4168_);
v_res_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_as_4166_, v_i_boxed_4172_, v_stop_boxed_4173_, v_b_4169_, v___y_4170_);
lean_dec_ref(v_as_4166_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(lean_object* v_as_4175_, size_t v_i_4176_, size_t v_stop_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_){
_start:
{
uint8_t v___x_4181_; 
v___x_4181_ = lean_usize_dec_eq(v_i_4176_, v_stop_4177_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = lean_array_uget_borrowed(v_as_4175_, v_i_4176_);
v___x_4183_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v___x_4182_, v___y_4179_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v_fst_4185_; lean_object* v_snd_4186_; size_t v___x_4187_; size_t v___x_4188_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v_fst_4185_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_fst_4185_);
v_snd_4186_ = lean_ctor_get(v_a_4184_, 1);
lean_inc(v_snd_4186_);
lean_dec(v_a_4184_);
v___x_4187_ = ((size_t)1ULL);
v___x_4188_ = lean_usize_add(v_i_4176_, v___x_4187_);
v_i_4176_ = v___x_4188_;
v_b_4178_ = v_fst_4185_;
v___y_4179_ = v_snd_4186_;
goto _start;
}
else
{
return v___x_4183_;
}
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_b_4178_);
lean_ctor_set(v___x_4190_, 1, v___y_4179_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1___boxed(lean_object* v_as_4192_, lean_object* v_i_4193_, lean_object* v_stop_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
size_t v_i_boxed_4198_; size_t v_stop_boxed_4199_; lean_object* v_res_4200_; 
v_i_boxed_4198_ = lean_unbox_usize(v_i_4193_);
lean_dec(v_i_4193_);
v_stop_boxed_4199_ = lean_unbox_usize(v_stop_4194_);
lean_dec(v_stop_4194_);
v_res_4200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_as_4192_, v_i_boxed_4198_, v_stop_boxed_4199_, v_b_4195_, v___y_4196_);
lean_dec_ref(v_as_4192_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(lean_object* v_as_4201_, size_t v_i_4202_, size_t v_stop_4203_, lean_object* v_b_4204_, lean_object* v___y_4205_){
_start:
{
uint8_t v___x_4207_; 
v___x_4207_ = lean_usize_dec_eq(v_i_4202_, v_stop_4203_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_array_uget_borrowed(v_as_4201_, v_i_4202_);
v___x_4209_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v___x_4208_, v___y_4205_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v_fst_4211_; lean_object* v_snd_4212_; size_t v___x_4213_; size_t v___x_4214_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v_fst_4211_ = lean_ctor_get(v_a_4210_, 0);
lean_inc(v_fst_4211_);
v_snd_4212_ = lean_ctor_get(v_a_4210_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_a_4210_);
v___x_4213_ = ((size_t)1ULL);
v___x_4214_ = lean_usize_add(v_i_4202_, v___x_4213_);
v_i_4202_ = v___x_4214_;
v_b_4204_ = v_fst_4211_;
v___y_4205_ = v_snd_4212_;
goto _start;
}
else
{
return v___x_4209_;
}
}
else
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_b_4204_);
lean_ctor_set(v___x_4216_, 1, v___y_4205_);
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2___boxed(lean_object* v_as_4218_, lean_object* v_i_4219_, lean_object* v_stop_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
size_t v_i_boxed_4224_; size_t v_stop_boxed_4225_; lean_object* v_res_4226_; 
v_i_boxed_4224_ = lean_unbox_usize(v_i_4219_);
lean_dec(v_i_4219_);
v_stop_boxed_4225_ = lean_unbox_usize(v_stop_4220_);
lean_dec(v_stop_4220_);
v_res_4226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_as_4218_, v_i_boxed_4224_, v_stop_boxed_4225_, v_b_4221_, v___y_4222_);
lean_dec_ref(v_as_4218_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(lean_object* v_data_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6));
v___x_4251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4238_, v___x_4250_);
if (lean_obj_tag(v___x_4251_) == 1)
{
lean_object* v_val_4252_; 
v_val_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_val_4252_);
lean_dec_ref_known(v___x_4251_, 1);
if (lean_obj_tag(v_val_4252_) == 4)
{
lean_object* v_elems_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_elems_4253_ = lean_ctor_get(v_val_4252_, 0);
lean_inc_ref(v_elems_4253_);
lean_dec_ref_known(v_val_4252_, 1);
v___x_4254_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_4255_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4238_, v___x_4254_);
if (lean_obj_tag(v___x_4255_) == 1)
{
lean_object* v_val_4256_; 
v_val_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v___x_4255_, 1);
if (lean_obj_tag(v_val_4256_) == 4)
{
lean_object* v_elems_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_elems_4257_ = lean_ctor_get(v_val_4256_, 0);
lean_inc_ref(v_elems_4257_);
lean_dec_ref_known(v_val_4256_, 1);
v___x_4258_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7));
v___x_4259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4238_, v___x_4258_);
if (lean_obj_tag(v___x_4259_) == 1)
{
lean_object* v_val_4260_; 
v_val_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_val_4260_);
lean_dec_ref_known(v___x_4259_, 1);
if (lean_obj_tag(v_val_4260_) == 4)
{
lean_object* v_elems_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4316_; 
v_elems_4261_ = lean_ctor_get(v_val_4260_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_val_4260_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4263_ = v_val_4260_;
v_isShared_4264_ = v_isSharedCheck_4316_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_elems_4261_);
lean_dec(v_val_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4316_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v_snd_4267_; lean_object* v___y_4287_; lean_object* v_snd_4291_; lean_object* v___y_4303_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4306_ = lean_array_get_size(v_elems_4253_);
v___x_4307_ = lean_nat_dec_lt(v___x_4265_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_dec_ref(v_elems_4253_);
v_snd_4291_ = v_a_4239_;
goto v___jp_4290_;
}
else
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = lean_box(0);
v___x_4309_ = lean_nat_dec_le(v___x_4306_, v___x_4306_);
if (v___x_4309_ == 0)
{
if (v___x_4307_ == 0)
{
lean_dec_ref(v_elems_4253_);
v_snd_4291_ = v_a_4239_;
goto v___jp_4290_;
}
else
{
size_t v___x_4310_; size_t v___x_4311_; lean_object* v___x_4312_; 
v___x_4310_ = ((size_t)0ULL);
v___x_4311_ = lean_usize_of_nat(v___x_4306_);
v___x_4312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4253_, v___x_4310_, v___x_4311_, v___x_4308_, v_a_4239_);
lean_dec_ref(v_elems_4253_);
v___y_4303_ = v___x_4312_;
goto v___jp_4302_;
}
}
else
{
size_t v___x_4313_; size_t v___x_4314_; lean_object* v___x_4315_; 
v___x_4313_ = ((size_t)0ULL);
v___x_4314_ = lean_usize_of_nat(v___x_4306_);
v___x_4315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4253_, v___x_4313_, v___x_4314_, v___x_4308_, v_a_4239_);
lean_dec_ref(v_elems_4253_);
v___y_4303_ = v___x_4315_;
goto v___jp_4302_;
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_array_get_size(v_elems_4261_);
v___x_4269_ = lean_box(0);
v___x_4270_ = lean_nat_dec_lt(v___x_4265_, v___x_4268_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; lean_object* v___x_4273_; 
lean_dec_ref(v_elems_4261_);
v___x_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4269_);
lean_ctor_set(v___x_4271_, 1, v_snd_4267_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set_tag(v___x_4263_, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4271_);
v___x_4273_ = v___x_4263_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
else
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_nat_dec_le(v___x_4268_, v___x_4268_);
if (v___x_4275_ == 0)
{
if (v___x_4270_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
lean_dec_ref(v_elems_4261_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4269_);
lean_ctor_set(v___x_4276_, 1, v_snd_4267_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set_tag(v___x_4263_, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4276_);
v___x_4278_ = v___x_4263_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
else
{
size_t v___x_4280_; size_t v___x_4281_; lean_object* v___x_4282_; 
lean_del_object(v___x_4263_);
v___x_4280_ = ((size_t)0ULL);
v___x_4281_ = lean_usize_of_nat(v___x_4268_);
v___x_4282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4261_, v___x_4280_, v___x_4281_, v___x_4269_, v_snd_4267_);
lean_dec_ref(v_elems_4261_);
return v___x_4282_;
}
}
else
{
size_t v___x_4283_; size_t v___x_4284_; lean_object* v___x_4285_; 
lean_del_object(v___x_4263_);
v___x_4283_ = ((size_t)0ULL);
v___x_4284_ = lean_usize_of_nat(v___x_4268_);
v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4261_, v___x_4283_, v___x_4284_, v___x_4269_, v_snd_4267_);
lean_dec_ref(v_elems_4261_);
return v___x_4285_;
}
}
}
v___jp_4286_:
{
if (lean_obj_tag(v___y_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v_snd_4289_; 
v_a_4288_ = lean_ctor_get(v___y_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___y_4287_, 1);
v_snd_4289_ = lean_ctor_get(v_a_4288_, 1);
lean_inc(v_snd_4289_);
lean_dec(v_a_4288_);
v_snd_4267_ = v_snd_4289_;
goto v___jp_4266_;
}
else
{
lean_del_object(v___x_4263_);
lean_dec_ref(v_elems_4261_);
return v___y_4287_;
}
}
v___jp_4290_:
{
lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4292_ = lean_array_get_size(v_elems_4257_);
v___x_4293_ = lean_nat_dec_lt(v___x_4265_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_dec_ref(v_elems_4257_);
v_snd_4267_ = v_snd_4291_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_nat_dec_le(v___x_4292_, v___x_4292_);
if (v___x_4295_ == 0)
{
if (v___x_4293_ == 0)
{
lean_dec_ref(v_elems_4257_);
v_snd_4267_ = v_snd_4291_;
goto v___jp_4266_;
}
else
{
size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = ((size_t)0ULL);
v___x_4297_ = lean_usize_of_nat(v___x_4292_);
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4257_, v___x_4296_, v___x_4297_, v___x_4294_, v_snd_4291_);
lean_dec_ref(v_elems_4257_);
v___y_4287_ = v___x_4298_;
goto v___jp_4286_;
}
}
else
{
size_t v___x_4299_; size_t v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = ((size_t)0ULL);
v___x_4300_ = lean_usize_of_nat(v___x_4292_);
v___x_4301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4257_, v___x_4299_, v___x_4300_, v___x_4294_, v_snd_4291_);
lean_dec_ref(v_elems_4257_);
v___y_4287_ = v___x_4301_;
goto v___jp_4286_;
}
}
}
v___jp_4302_:
{
if (lean_obj_tag(v___y_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v_snd_4305_; 
v_a_4304_ = lean_ctor_get(v___y_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___y_4303_, 1);
v_snd_4305_ = lean_ctor_get(v_a_4304_, 1);
lean_inc(v_snd_4305_);
lean_dec(v_a_4304_);
v_snd_4291_ = v_snd_4305_;
goto v___jp_4290_;
}
else
{
lean_del_object(v___x_4263_);
lean_dec_ref(v_elems_4261_);
lean_dec_ref(v_elems_4257_);
return v___y_4303_;
}
}
}
}
else
{
lean_dec(v_val_4260_);
lean_dec_ref(v_elems_4257_);
lean_dec_ref(v_elems_4253_);
lean_dec_ref(v_a_4239_);
goto v___jp_4241_;
}
}
else
{
lean_dec(v___x_4259_);
lean_dec_ref(v_elems_4257_);
lean_dec_ref(v_elems_4253_);
lean_dec_ref(v_a_4239_);
goto v___jp_4241_;
}
}
else
{
lean_dec(v_val_4256_);
lean_dec_ref(v_elems_4253_);
lean_dec_ref(v_a_4239_);
goto v___jp_4244_;
}
}
else
{
lean_dec(v___x_4255_);
lean_dec_ref(v_elems_4253_);
lean_dec_ref(v_a_4239_);
goto v___jp_4244_;
}
}
else
{
lean_dec(v_val_4252_);
lean_dec_ref(v_a_4239_);
goto v___jp_4247_;
}
}
else
{
lean_dec(v___x_4251_);
lean_dec_ref(v_a_4239_);
goto v___jp_4247_;
}
v___jp_4241_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1));
v___x_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
return v___x_4243_;
}
v___jp_4244_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3));
v___x_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
v___jp_4247_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5));
v___x_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___boxed(lean_object* v_data_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_data_4317_, v_a_4318_);
lean_dec(v_data_4317_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(lean_object* v_init_4321_, lean_object* v_x_4322_){
_start:
{
if (lean_obj_tag(v_x_4322_) == 0)
{
lean_object* v_k_4323_; lean_object* v_v_4324_; lean_object* v_l_4325_; lean_object* v_r_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v_k_4323_ = lean_ctor_get(v_x_4322_, 1);
v_v_4324_ = lean_ctor_get(v_x_4322_, 2);
v_l_4325_ = lean_ctor_get(v_x_4322_, 3);
v_r_4326_ = lean_ctor_get(v_x_4322_, 4);
v___x_4327_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v_init_4321_, v_r_4326_);
lean_inc(v_v_4324_);
lean_inc(v_k_4323_);
v___x_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_k_4323_);
lean_ctor_set(v___x_4328_, 1, v_v_4324_);
v___x_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set(v___x_4329_, 1, v___x_4327_);
v_init_4321_ = v___x_4329_;
v_x_4322_ = v_l_4325_;
goto _start;
}
else
{
return v_init_4321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3___boxed(lean_object* v_init_4331_, lean_object* v_x_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v_init_4331_, v_x_4332_);
lean_dec(v_x_4332_);
return v_res_4333_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(lean_object* v_m_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_buckets_4336_; lean_object* v___x_4337_; uint64_t v___x_4338_; uint64_t v___x_4339_; uint64_t v___x_4340_; uint64_t v_fold_4341_; uint64_t v___x_4342_; uint64_t v___x_4343_; uint64_t v___x_4344_; size_t v___x_4345_; size_t v___x_4346_; size_t v___x_4347_; size_t v___x_4348_; size_t v___x_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; 
v_buckets_4336_ = lean_ctor_get(v_m_4334_, 1);
v___x_4337_ = lean_array_get_size(v_buckets_4336_);
v___x_4338_ = lean_uint64_of_nat(v_a_4335_);
v___x_4339_ = 32ULL;
v___x_4340_ = lean_uint64_shift_right(v___x_4338_, v___x_4339_);
v_fold_4341_ = lean_uint64_xor(v___x_4338_, v___x_4340_);
v___x_4342_ = 16ULL;
v___x_4343_ = lean_uint64_shift_right(v_fold_4341_, v___x_4342_);
v___x_4344_ = lean_uint64_xor(v_fold_4341_, v___x_4343_);
v___x_4345_ = lean_uint64_to_usize(v___x_4344_);
v___x_4346_ = lean_usize_of_nat(v___x_4337_);
v___x_4347_ = ((size_t)1ULL);
v___x_4348_ = lean_usize_sub(v___x_4346_, v___x_4347_);
v___x_4349_ = lean_usize_land(v___x_4345_, v___x_4348_);
v___x_4350_ = lean_array_uget_borrowed(v_buckets_4336_, v___x_4349_);
v___x_4351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_4335_, v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg___boxed(lean_object* v_m_4352_, lean_object* v_a_4353_){
_start:
{
uint8_t v_res_4354_; lean_object* v_r_4355_; 
v_res_4354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_m_4352_, v_a_4353_);
lean_dec(v_a_4353_);
lean_dec_ref(v_m_4352_);
v_r_4355_ = lean_box(v_res_4354_);
return v_r_4355_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(lean_object* v_x_4357_, lean_object* v_x_4358_){
_start:
{
if (lean_obj_tag(v_x_4358_) == 0)
{
return v_x_4357_;
}
else
{
lean_object* v_head_4359_; lean_object* v_tail_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_head_4359_ = lean_ctor_get(v_x_4358_, 0);
v_tail_4360_ = lean_ctor_get(v_x_4358_, 1);
v___x_4361_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0));
v___x_4362_ = lean_string_append(v_x_4357_, v___x_4361_);
v___x_4363_ = lean_string_append(v___x_4362_, v_head_4359_);
v_x_4357_ = v___x_4363_;
v_x_4358_ = v_tail_4360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___boxed(lean_object* v_x_4365_, lean_object* v_x_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v_x_4365_, v_x_4366_);
lean_dec(v_x_4366_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object* v_x_4371_){
_start:
{
if (lean_obj_tag(v_x_4371_) == 0)
{
lean_object* v___x_4372_; 
v___x_4372_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0));
return v___x_4372_;
}
else
{
lean_object* v_tail_4373_; 
v_tail_4373_ = lean_ctor_get(v_x_4371_, 1);
if (lean_obj_tag(v_tail_4373_) == 0)
{
lean_object* v_head_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_head_4374_ = lean_ctor_get(v_x_4371_, 0);
v___x_4375_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4376_ = lean_string_append(v___x_4375_, v_head_4374_);
v___x_4377_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2));
v___x_4378_ = lean_string_append(v___x_4376_, v___x_4377_);
return v___x_4378_;
}
else
{
lean_object* v_head_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; uint32_t v___x_4383_; lean_object* v___x_4384_; 
v_head_4379_ = lean_ctor_get(v_x_4371_, 0);
v___x_4380_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4381_ = lean_string_append(v___x_4380_, v_head_4379_);
v___x_4382_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v___x_4381_, v_tail_4373_);
v___x_4383_ = 93;
v___x_4384_ = lean_string_push(v___x_4382_, v___x_4383_);
return v___x_4384_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___boxed(lean_object* v_x_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_x_4385_);
lean_dec(v_x_4385_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(lean_object* v_init_4387_, lean_object* v_x_4388_){
_start:
{
if (lean_obj_tag(v_x_4388_) == 0)
{
lean_object* v_k_4389_; lean_object* v_l_4390_; lean_object* v_r_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_k_4389_ = lean_ctor_get(v_x_4388_, 1);
v_l_4390_ = lean_ctor_get(v_x_4388_, 3);
v_r_4391_ = lean_ctor_get(v_x_4388_, 4);
v___x_4392_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4387_, v_r_4391_);
lean_inc(v_k_4389_);
v___x_4393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_k_4389_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v_init_4387_ = v___x_4393_;
v_x_4388_ = v_l_4390_;
goto _start;
}
else
{
return v_init_4387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0___boxed(lean_object* v_init_4395_, lean_object* v_x_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4395_, v_x_4396_);
lean_dec(v_x_4396_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(lean_object* v_line_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_LeanExport_Json_parse(v_line_4423_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v_a_4424_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4437_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4437_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4431_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0));
v___x_4432_ = lean_string_append(v___x_4431_, v_a_4427_);
lean_dec(v_a_4427_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set_tag(v___x_4429_, 18);
lean_ctor_set(v___x_4429_, 0, v___x_4432_);
v___x_4434_ = v___x_4429_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_5531_; 
v_a_4438_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_4440_ = v___x_4426_;
v_isShared_4441_ = v_isSharedCheck_5531_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4426_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_5531_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
if (lean_obj_tag(v_a_4438_) == 5)
{
lean_object* v_kvPairs_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_5526_; 
v_kvPairs_4442_ = lean_ctor_get(v_a_4438_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v_a_4438_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_4444_ = v_a_4438_;
v_isShared_4445_ = v_isSharedCheck_5526_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_kvPairs_4442_);
lean_dec(v_a_4438_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_5526_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_fst_4459_; lean_object* v_snd_4460_; lean_object* v_tail_4461_; lean_object* v___y_5493_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5498_ = lean_box(0);
v___x_5499_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v___x_5498_, v_kvPairs_4442_);
if (lean_obj_tag(v___x_5499_) == 1)
{
lean_object* v_tail_5500_; 
v_tail_5500_ = lean_ctor_get(v___x_5499_, 1);
lean_inc(v_tail_5500_);
if (lean_obj_tag(v_tail_5500_) == 1)
{
lean_object* v_head_5501_; lean_object* v_head_5502_; lean_object* v_tail_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5524_; 
v_head_5501_ = lean_ctor_get(v_tail_5500_, 0);
lean_inc(v_head_5501_);
v_head_5502_ = lean_ctor_get(v___x_5499_, 0);
v_tail_5503_ = lean_ctor_get(v_tail_5500_, 1);
v_isSharedCheck_5524_ = !lean_is_exclusive(v_tail_5500_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; 
v_unused_5525_ = lean_ctor_get(v_tail_5500_, 0);
lean_dec(v_unused_5525_);
v___x_5505_ = v_tail_5500_;
v_isShared_5506_ = v_isSharedCheck_5524_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_tail_5503_);
lean_dec(v_tail_5500_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5524_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v_fst_5507_; lean_object* v_snd_5508_; lean_object* v___x_5509_; uint8_t v___x_5510_; 
v_fst_5507_ = lean_ctor_get(v_head_5501_, 0);
lean_inc(v_fst_5507_);
v_snd_5508_ = lean_ctor_get(v_head_5501_, 1);
lean_inc(v_snd_5508_);
lean_dec(v_head_5501_);
v___x_5509_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_5510_ = lean_string_dec_eq(v_fst_5507_, v___x_5509_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5511_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_5512_ = lean_string_dec_eq(v_fst_5507_, v___x_5511_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; uint8_t v___x_5514_; 
v___x_5513_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_5514_ = lean_string_dec_eq(v_fst_5507_, v___x_5513_);
lean_dec(v_fst_5507_);
if (v___x_5514_ == 0)
{
lean_dec(v_snd_5508_);
lean_del_object(v___x_5505_);
lean_dec(v_tail_5503_);
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
else
{
if (lean_obj_tag(v_tail_5503_) == 0)
{
lean_object* v___x_5516_; 
lean_inc(v_head_5502_);
lean_dec_ref_known(v___x_5499_, 2);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v_head_5502_);
v___x_5516_ = v___x_5505_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_head_5502_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v_tail_5503_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
v_fst_4459_ = v___x_5513_;
v_snd_4460_ = v_snd_5508_;
v_tail_4461_ = v___x_5516_;
goto v___jp_4458_;
}
}
else
{
lean_dec(v_snd_5508_);
lean_del_object(v___x_5505_);
lean_dec(v_tail_5503_);
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
}
}
else
{
lean_dec(v_fst_5507_);
if (lean_obj_tag(v_tail_5503_) == 0)
{
lean_object* v___x_5519_; 
lean_inc(v_head_5502_);
lean_dec_ref_known(v___x_5499_, 2);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v_head_5502_);
v___x_5519_ = v___x_5505_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_head_5502_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_tail_5503_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
v_fst_4459_ = v___x_5511_;
v_snd_4460_ = v_snd_5508_;
v_tail_4461_ = v___x_5519_;
goto v___jp_4458_;
}
}
else
{
lean_dec(v_snd_5508_);
lean_del_object(v___x_5505_);
lean_dec(v_tail_5503_);
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
}
}
else
{
lean_dec(v_fst_5507_);
if (lean_obj_tag(v_tail_5503_) == 0)
{
lean_object* v___x_5522_; 
lean_inc(v_head_5502_);
lean_dec_ref_known(v___x_5499_, 2);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v_head_5502_);
v___x_5522_ = v___x_5505_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_head_5502_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_tail_5503_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
v_fst_4459_ = v___x_5509_;
v_snd_4460_ = v_snd_5508_;
v_tail_4461_ = v___x_5522_;
goto v___jp_4458_;
}
}
else
{
lean_dec(v_snd_5508_);
lean_del_object(v___x_5505_);
lean_dec(v_tail_5503_);
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
}
}
}
else
{
lean_dec(v_tail_5500_);
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
}
else
{
v___y_5493_ = v___x_5499_;
goto v___jp_5492_;
}
v___jp_4446_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4447_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0));
v___x_4448_ = lean_box(0);
v___x_4449_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v___x_4448_, v_kvPairs_4442_);
lean_dec(v_kvPairs_4442_);
v___x_4450_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v___x_4449_);
lean_dec(v___x_4449_);
v___x_4451_ = lean_string_append(v___x_4447_, v___x_4450_);
lean_dec_ref(v___x_4450_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set_tag(v___x_4444_, 18);
lean_ctor_set(v___x_4444_, 0, v___x_4451_);
v___x_4453_ = v___x_4444_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4453_);
v___x_4455_ = v___x_4440_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
v___jp_4458_:
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_4463_ = lean_string_dec_eq(v_fst_4459_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_4465_ = lean_string_dec_eq(v_fst_4459_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; uint8_t v___x_4467_; 
v___x_4466_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_4467_ = lean_string_dec_eq(v_fst_4459_, v___x_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; uint8_t v___x_4469_; 
v___x_4468_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4));
v___x_4469_ = lean_string_dec_eq(v_fst_4459_, v___x_4468_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4470_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5));
v___x_4471_ = lean_string_dec_eq(v_fst_4459_, v___x_4470_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4472_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6));
v___x_4473_ = lean_string_dec_eq(v_fst_4459_, v___x_4472_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4474_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_4475_ = lean_string_dec_eq(v_fst_4459_, v___x_4474_);
if (v___x_4475_ == 0)
{
lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4476_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7));
v___x_4477_ = lean_string_dec_eq(v_fst_4459_, v___x_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8));
v___x_4479_ = lean_string_dec_eq(v_fst_4459_, v___x_4478_);
lean_dec_ref(v_fst_4459_);
if (v___x_4479_ == 0)
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4480_; lean_object* v___x_4481_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4480_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4480_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4481_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_kvPairs_4480_, v_a_4424_);
lean_dec(v_kvPairs_4480_);
return v___x_4481_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4482_; lean_object* v___x_4483_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4482_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4482_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4483_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_kvPairs_4482_, v_a_4424_);
lean_dec(v_kvPairs_4482_);
return v___x_4483_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4484_; lean_object* v___x_4485_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4484_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4484_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4485_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_kvPairs_4484_, v_a_4424_);
lean_dec(v_kvPairs_4484_);
return v___x_4485_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4486_; lean_object* v___x_4487_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4486_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4486_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4487_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_kvPairs_4486_, v_a_4424_);
lean_dec(v_kvPairs_4486_);
return v___x_4487_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4488_; lean_object* v___x_4489_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4488_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4488_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4489_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_kvPairs_4488_, v_a_4424_);
lean_dec(v_kvPairs_4488_);
return v___x_4489_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 5)
{
if (lean_obj_tag(v_tail_4461_) == 0)
{
lean_object* v_kvPairs_4490_; lean_object* v___x_4491_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v_kvPairs_4490_ = lean_ctor_get(v_snd_4460_, 0);
lean_inc(v_kvPairs_4490_);
lean_dec_ref_known(v_snd_4460_, 1);
v___x_4491_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_kvPairs_4490_, v_a_4424_);
lean_dec(v_kvPairs_4490_);
return v___x_4491_;
}
else
{
lean_dec_ref_known(v_snd_4460_, 1);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 2)
{
lean_object* v_n_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_5123_; 
v_n_4492_ = lean_ctor_get(v_snd_4460_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v_snd_4460_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_4494_ = v_snd_4460_;
v_isShared_4495_ = v_isSharedCheck_5123_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_n_4492_);
lean_dec(v_snd_4460_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_5123_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v_mantissa_4496_; lean_object* v_exponent_4497_; lean_object* v_natZero_4498_; lean_object* v_intZero_4499_; uint8_t v_isNeg_4500_; 
v_mantissa_4496_ = lean_ctor_get(v_n_4492_, 0);
lean_inc(v_mantissa_4496_);
v_exponent_4497_ = lean_ctor_get(v_n_4492_, 1);
lean_inc(v_exponent_4497_);
lean_dec_ref(v_n_4492_);
v_natZero_4498_ = lean_unsigned_to_nat(0u);
v_intZero_4499_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4500_ = lean_int_dec_lt(v_mantissa_4496_, v_intZero_4499_);
if (v_isNeg_4500_ == 0)
{
uint8_t v___x_4501_; 
v___x_4501_ = lean_nat_dec_eq(v_exponent_4497_, v_natZero_4498_);
lean_dec(v_exponent_4497_);
if (v___x_4501_ == 0)
{
lean_dec(v_mantissa_4496_);
lean_del_object(v___x_4494_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_4461_) == 1)
{
lean_object* v_head_4502_; lean_object* v_tail_4503_; lean_object* v_fst_4504_; lean_object* v_snd_4505_; lean_object* v_a_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v_head_4502_ = lean_ctor_get(v_tail_4461_, 0);
lean_inc(v_head_4502_);
v_tail_4503_ = lean_ctor_get(v_tail_4461_, 1);
lean_inc(v_tail_4503_);
lean_dec_ref_known(v_tail_4461_, 2);
v_fst_4504_ = lean_ctor_get(v_head_4502_, 0);
lean_inc(v_fst_4504_);
v_snd_4505_ = lean_ctor_get(v_head_4502_, 1);
lean_inc(v_snd_4505_);
lean_dec(v_head_4502_);
v_a_4506_ = lean_nat_abs(v_mantissa_4496_);
lean_dec(v_mantissa_4496_);
v___x_4507_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9));
v___x_4508_ = lean_string_dec_eq(v_fst_4504_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10));
v___x_4510_ = lean_string_dec_eq(v_fst_4504_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11));
v___x_4512_ = lean_string_dec_eq(v_fst_4504_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12));
v___x_4514_ = lean_string_dec_eq(v_fst_4504_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13));
v___x_4516_ = lean_string_dec_eq(v_fst_4504_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4517_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14));
v___x_4518_ = lean_string_dec_eq(v_fst_4504_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15));
v___x_4520_ = lean_string_dec_eq(v_fst_4504_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4521_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16));
v___x_4522_ = lean_string_dec_eq(v_fst_4504_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; uint8_t v___x_4524_; 
v___x_4523_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17));
v___x_4524_ = lean_string_dec_eq(v_fst_4504_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18));
v___x_4526_ = lean_string_dec_eq(v_fst_4504_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19));
v___x_4528_ = lean_string_dec_eq(v_fst_4504_, v___x_4527_);
lean_dec(v_fst_4504_);
if (v___x_4528_ == 0)
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4529_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4529_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4574_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4574_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4574_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_snd_4534_; lean_object* v_fst_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4573_; 
v_snd_4534_ = lean_ctor_get(v_a_4530_, 1);
v_fst_4535_ = lean_ctor_get(v_a_4530_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v_a_4530_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4537_ = v_a_4530_;
v_isShared_4538_ = v_isSharedCheck_4573_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_snd_4534_);
lean_inc(v_fst_4535_);
lean_dec(v_a_4530_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4573_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v_stream_4539_; lean_object* v_nameMap_4540_; lean_object* v_levelMap_4541_; lean_object* v_exprMap_4542_; lean_object* v_recursorRuleMap_4543_; lean_object* v_constMap_4544_; lean_object* v_constOrder_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4572_; 
v_stream_4539_ = lean_ctor_get(v_snd_4534_, 0);
v_nameMap_4540_ = lean_ctor_get(v_snd_4534_, 1);
v_levelMap_4541_ = lean_ctor_get(v_snd_4534_, 2);
v_exprMap_4542_ = lean_ctor_get(v_snd_4534_, 3);
v_recursorRuleMap_4543_ = lean_ctor_get(v_snd_4534_, 4);
v_constMap_4544_ = lean_ctor_get(v_snd_4534_, 5);
v_constOrder_4545_ = lean_ctor_get(v_snd_4534_, 6);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_snd_4534_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4547_ = v_snd_4534_;
v_isShared_4548_ = v_isSharedCheck_4572_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_constOrder_4545_);
lean_inc(v_constMap_4544_);
lean_inc(v_recursorRuleMap_4543_);
lean_inc(v_exprMap_4542_);
lean_inc(v_levelMap_4541_);
lean_inc(v_nameMap_4540_);
lean_inc(v_stream_4539_);
lean_dec(v_snd_4534_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4572_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
uint8_t v___x_4549_; 
v___x_4549_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4542_, v_a_4506_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
lean_del_object(v___x_4494_);
v___x_4550_ = lean_box(0);
v___x_4551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4542_, v_a_4506_, v_fst_4535_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 3, v___x_4551_);
v___x_4553_ = v___x_4547_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_stream_4539_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_nameMap_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_levelMap_4541_);
lean_ctor_set(v_reuseFailAlloc_4560_, 3, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4560_, 4, v_recursorRuleMap_4543_);
lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_constMap_4544_);
lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_constOrder_4545_);
v___x_4553_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 1, v___x_4553_);
lean_ctor_set(v___x_4537_, 0, v___x_4550_);
v___x_4555_ = v___x_4537_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4557_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4555_);
v___x_4557_ = v___x_4532_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
lean_del_object(v___x_4547_);
lean_dec_ref(v_constOrder_4545_);
lean_dec_ref(v_constMap_4544_);
lean_dec_ref(v_recursorRuleMap_4543_);
lean_dec_ref(v_exprMap_4542_);
lean_dec_ref(v_levelMap_4541_);
lean_dec_ref(v_nameMap_4540_);
lean_dec_ref(v_stream_4539_);
lean_del_object(v___x_4537_);
lean_dec(v_fst_4535_);
v___x_4561_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4562_ = l_Nat_reprFast(v_a_4506_);
v___x_4563_ = lean_string_append(v___x_4561_, v___x_4562_);
lean_dec_ref(v___x_4562_);
v___x_4564_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4565_ = lean_string_append(v___x_4563_, v___x_4564_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4565_);
v___x_4567_ = v___x_4494_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4569_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set_tag(v___x_4532_, 1);
lean_ctor_set(v___x_4532_, 0, v___x_4567_);
v___x_4569_ = v___x_4532_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4575_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4529_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4529_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4583_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4583_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_snd_4505_, v_a_4424_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4628_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4628_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4628_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_snd_4588_; lean_object* v_fst_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4627_; 
v_snd_4588_ = lean_ctor_get(v_a_4584_, 1);
v_fst_4589_ = lean_ctor_get(v_a_4584_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_a_4584_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4591_ = v_a_4584_;
v_isShared_4592_ = v_isSharedCheck_4627_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_snd_4588_);
lean_inc(v_fst_4589_);
lean_dec(v_a_4584_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4627_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v_stream_4593_; lean_object* v_nameMap_4594_; lean_object* v_levelMap_4595_; lean_object* v_exprMap_4596_; lean_object* v_recursorRuleMap_4597_; lean_object* v_constMap_4598_; lean_object* v_constOrder_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4626_; 
v_stream_4593_ = lean_ctor_get(v_snd_4588_, 0);
v_nameMap_4594_ = lean_ctor_get(v_snd_4588_, 1);
v_levelMap_4595_ = lean_ctor_get(v_snd_4588_, 2);
v_exprMap_4596_ = lean_ctor_get(v_snd_4588_, 3);
v_recursorRuleMap_4597_ = lean_ctor_get(v_snd_4588_, 4);
v_constMap_4598_ = lean_ctor_get(v_snd_4588_, 5);
v_constOrder_4599_ = lean_ctor_get(v_snd_4588_, 6);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_snd_4588_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4601_ = v_snd_4588_;
v_isShared_4602_ = v_isSharedCheck_4626_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_constOrder_4599_);
lean_inc(v_constMap_4598_);
lean_inc(v_recursorRuleMap_4597_);
lean_inc(v_exprMap_4596_);
lean_inc(v_levelMap_4595_);
lean_inc(v_nameMap_4594_);
lean_inc(v_stream_4593_);
lean_dec(v_snd_4588_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4626_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
uint8_t v___x_4603_; 
v___x_4603_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4596_, v_a_4506_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
lean_del_object(v___x_4494_);
v___x_4604_ = lean_box(0);
v___x_4605_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4596_, v_a_4506_, v_fst_4589_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 3, v___x_4605_);
v___x_4607_ = v___x_4601_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_stream_4593_);
lean_ctor_set(v_reuseFailAlloc_4614_, 1, v_nameMap_4594_);
lean_ctor_set(v_reuseFailAlloc_4614_, 2, v_levelMap_4595_);
lean_ctor_set(v_reuseFailAlloc_4614_, 3, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4614_, 4, v_recursorRuleMap_4597_);
lean_ctor_set(v_reuseFailAlloc_4614_, 5, v_constMap_4598_);
lean_ctor_set(v_reuseFailAlloc_4614_, 6, v_constOrder_4599_);
v___x_4607_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4609_; 
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 1, v___x_4607_);
lean_ctor_set(v___x_4591_, 0, v___x_4604_);
v___x_4609_ = v___x_4591_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v___x_4609_);
v___x_4611_ = v___x_4586_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
lean_del_object(v___x_4601_);
lean_dec_ref(v_constOrder_4599_);
lean_dec_ref(v_constMap_4598_);
lean_dec_ref(v_recursorRuleMap_4597_);
lean_dec_ref(v_exprMap_4596_);
lean_dec_ref(v_levelMap_4595_);
lean_dec_ref(v_nameMap_4594_);
lean_dec_ref(v_stream_4593_);
lean_del_object(v___x_4591_);
lean_dec(v_fst_4589_);
v___x_4615_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4616_ = l_Nat_reprFast(v_a_4506_);
v___x_4617_ = lean_string_append(v___x_4615_, v___x_4616_);
lean_dec_ref(v___x_4616_);
v___x_4618_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4619_ = lean_string_append(v___x_4617_, v___x_4618_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4619_);
v___x_4621_ = v___x_4494_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4623_; 
if (v_isShared_4587_ == 0)
{
lean_ctor_set_tag(v___x_4586_, 1);
lean_ctor_set(v___x_4586_, 0, v___x_4621_);
v___x_4623_ = v___x_4586_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4629_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4583_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4583_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4637_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4637_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_snd_4505_, v_a_4424_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4682_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4640_ = v___x_4637_;
v_isShared_4641_ = v_isSharedCheck_4682_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4637_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4682_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v_snd_4642_; lean_object* v_fst_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4681_; 
v_snd_4642_ = lean_ctor_get(v_a_4638_, 1);
v_fst_4643_ = lean_ctor_get(v_a_4638_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_a_4638_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4645_ = v_a_4638_;
v_isShared_4646_ = v_isSharedCheck_4681_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_snd_4642_);
lean_inc(v_fst_4643_);
lean_dec(v_a_4638_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4681_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v_stream_4647_; lean_object* v_nameMap_4648_; lean_object* v_levelMap_4649_; lean_object* v_exprMap_4650_; lean_object* v_recursorRuleMap_4651_; lean_object* v_constMap_4652_; lean_object* v_constOrder_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4680_; 
v_stream_4647_ = lean_ctor_get(v_snd_4642_, 0);
v_nameMap_4648_ = lean_ctor_get(v_snd_4642_, 1);
v_levelMap_4649_ = lean_ctor_get(v_snd_4642_, 2);
v_exprMap_4650_ = lean_ctor_get(v_snd_4642_, 3);
v_recursorRuleMap_4651_ = lean_ctor_get(v_snd_4642_, 4);
v_constMap_4652_ = lean_ctor_get(v_snd_4642_, 5);
v_constOrder_4653_ = lean_ctor_get(v_snd_4642_, 6);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_snd_4642_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4655_ = v_snd_4642_;
v_isShared_4656_ = v_isSharedCheck_4680_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_constOrder_4653_);
lean_inc(v_constMap_4652_);
lean_inc(v_recursorRuleMap_4651_);
lean_inc(v_exprMap_4650_);
lean_inc(v_levelMap_4649_);
lean_inc(v_nameMap_4648_);
lean_inc(v_stream_4647_);
lean_dec(v_snd_4642_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4680_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
uint8_t v___x_4657_; 
v___x_4657_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4650_, v_a_4506_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
lean_del_object(v___x_4494_);
v___x_4658_ = lean_box(0);
v___x_4659_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4650_, v_a_4506_, v_fst_4643_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 3, v___x_4659_);
v___x_4661_ = v___x_4655_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_stream_4647_);
lean_ctor_set(v_reuseFailAlloc_4668_, 1, v_nameMap_4648_);
lean_ctor_set(v_reuseFailAlloc_4668_, 2, v_levelMap_4649_);
lean_ctor_set(v_reuseFailAlloc_4668_, 3, v___x_4659_);
lean_ctor_set(v_reuseFailAlloc_4668_, 4, v_recursorRuleMap_4651_);
lean_ctor_set(v_reuseFailAlloc_4668_, 5, v_constMap_4652_);
lean_ctor_set(v_reuseFailAlloc_4668_, 6, v_constOrder_4653_);
v___x_4661_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
lean_object* v___x_4663_; 
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 1, v___x_4661_);
lean_ctor_set(v___x_4645_, 0, v___x_4658_);
v___x_4663_ = v___x_4645_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4665_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 0, v___x_4663_);
v___x_4665_ = v___x_4640_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4675_; 
lean_del_object(v___x_4655_);
lean_dec_ref(v_constOrder_4653_);
lean_dec_ref(v_constMap_4652_);
lean_dec_ref(v_recursorRuleMap_4651_);
lean_dec_ref(v_exprMap_4650_);
lean_dec_ref(v_levelMap_4649_);
lean_dec_ref(v_nameMap_4648_);
lean_dec_ref(v_stream_4647_);
lean_del_object(v___x_4645_);
lean_dec(v_fst_4643_);
v___x_4669_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4670_ = l_Nat_reprFast(v_a_4506_);
v___x_4671_ = lean_string_append(v___x_4669_, v___x_4670_);
lean_dec_ref(v___x_4670_);
v___x_4672_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4673_ = lean_string_append(v___x_4671_, v___x_4672_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4673_);
v___x_4675_ = v___x_4494_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
lean_object* v___x_4677_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set_tag(v___x_4640_, 1);
lean_ctor_set(v___x_4640_, 0, v___x_4675_);
v___x_4677_ = v___x_4640_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4675_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4683_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4637_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4637_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4691_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4691_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4736_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4736_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4736_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_snd_4696_; lean_object* v_fst_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4735_; 
v_snd_4696_ = lean_ctor_get(v_a_4692_, 1);
v_fst_4697_ = lean_ctor_get(v_a_4692_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_a_4692_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4699_ = v_a_4692_;
v_isShared_4700_ = v_isSharedCheck_4735_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_snd_4696_);
lean_inc(v_fst_4697_);
lean_dec(v_a_4692_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4735_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_stream_4701_; lean_object* v_nameMap_4702_; lean_object* v_levelMap_4703_; lean_object* v_exprMap_4704_; lean_object* v_recursorRuleMap_4705_; lean_object* v_constMap_4706_; lean_object* v_constOrder_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4734_; 
v_stream_4701_ = lean_ctor_get(v_snd_4696_, 0);
v_nameMap_4702_ = lean_ctor_get(v_snd_4696_, 1);
v_levelMap_4703_ = lean_ctor_get(v_snd_4696_, 2);
v_exprMap_4704_ = lean_ctor_get(v_snd_4696_, 3);
v_recursorRuleMap_4705_ = lean_ctor_get(v_snd_4696_, 4);
v_constMap_4706_ = lean_ctor_get(v_snd_4696_, 5);
v_constOrder_4707_ = lean_ctor_get(v_snd_4696_, 6);
v_isSharedCheck_4734_ = !lean_is_exclusive(v_snd_4696_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4709_ = v_snd_4696_;
v_isShared_4710_ = v_isSharedCheck_4734_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_constOrder_4707_);
lean_inc(v_constMap_4706_);
lean_inc(v_recursorRuleMap_4705_);
lean_inc(v_exprMap_4704_);
lean_inc(v_levelMap_4703_);
lean_inc(v_nameMap_4702_);
lean_inc(v_stream_4701_);
lean_dec(v_snd_4696_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4734_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
uint8_t v___x_4711_; 
v___x_4711_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4704_, v_a_4506_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4715_; 
lean_del_object(v___x_4494_);
v___x_4712_ = lean_box(0);
v___x_4713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4704_, v_a_4506_, v_fst_4697_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 3, v___x_4713_);
v___x_4715_ = v___x_4709_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_stream_4701_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_nameMap_4702_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_levelMap_4703_);
lean_ctor_set(v_reuseFailAlloc_4722_, 3, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 4, v_recursorRuleMap_4705_);
lean_ctor_set(v_reuseFailAlloc_4722_, 5, v_constMap_4706_);
lean_ctor_set(v_reuseFailAlloc_4722_, 6, v_constOrder_4707_);
v___x_4715_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4717_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v___x_4715_);
lean_ctor_set(v___x_4699_, 0, v___x_4712_);
v___x_4717_ = v___x_4699_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4719_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4717_);
v___x_4719_ = v___x_4694_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
else
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4729_; 
lean_del_object(v___x_4709_);
lean_dec_ref(v_constOrder_4707_);
lean_dec_ref(v_constMap_4706_);
lean_dec_ref(v_recursorRuleMap_4705_);
lean_dec_ref(v_exprMap_4704_);
lean_dec_ref(v_levelMap_4703_);
lean_dec_ref(v_nameMap_4702_);
lean_dec_ref(v_stream_4701_);
lean_del_object(v___x_4699_);
lean_dec(v_fst_4697_);
v___x_4723_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4724_ = l_Nat_reprFast(v_a_4506_);
v___x_4725_ = lean_string_append(v___x_4723_, v___x_4724_);
lean_dec_ref(v___x_4724_);
v___x_4726_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4727_ = lean_string_append(v___x_4725_, v___x_4726_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4727_);
v___x_4729_ = v___x_4494_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4727_);
v___x_4729_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4731_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set_tag(v___x_4694_, 1);
lean_ctor_set(v___x_4694_, 0, v___x_4729_);
v___x_4731_ = v___x_4694_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4729_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4737_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4691_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4691_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4745_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4745_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4790_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4790_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4790_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v_snd_4750_; lean_object* v_fst_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4789_; 
v_snd_4750_ = lean_ctor_get(v_a_4746_, 1);
v_fst_4751_ = lean_ctor_get(v_a_4746_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_a_4746_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4753_ = v_a_4746_;
v_isShared_4754_ = v_isSharedCheck_4789_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_snd_4750_);
lean_inc(v_fst_4751_);
lean_dec(v_a_4746_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4789_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v_stream_4755_; lean_object* v_nameMap_4756_; lean_object* v_levelMap_4757_; lean_object* v_exprMap_4758_; lean_object* v_recursorRuleMap_4759_; lean_object* v_constMap_4760_; lean_object* v_constOrder_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4788_; 
v_stream_4755_ = lean_ctor_get(v_snd_4750_, 0);
v_nameMap_4756_ = lean_ctor_get(v_snd_4750_, 1);
v_levelMap_4757_ = lean_ctor_get(v_snd_4750_, 2);
v_exprMap_4758_ = lean_ctor_get(v_snd_4750_, 3);
v_recursorRuleMap_4759_ = lean_ctor_get(v_snd_4750_, 4);
v_constMap_4760_ = lean_ctor_get(v_snd_4750_, 5);
v_constOrder_4761_ = lean_ctor_get(v_snd_4750_, 6);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_snd_4750_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4763_ = v_snd_4750_;
v_isShared_4764_ = v_isSharedCheck_4788_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_constOrder_4761_);
lean_inc(v_constMap_4760_);
lean_inc(v_recursorRuleMap_4759_);
lean_inc(v_exprMap_4758_);
lean_inc(v_levelMap_4757_);
lean_inc(v_nameMap_4756_);
lean_inc(v_stream_4755_);
lean_dec(v_snd_4750_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4788_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
uint8_t v___x_4765_; 
v___x_4765_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4758_, v_a_4506_);
if (v___x_4765_ == 0)
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
lean_del_object(v___x_4494_);
v___x_4766_ = lean_box(0);
v___x_4767_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4758_, v_a_4506_, v_fst_4751_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 3, v___x_4767_);
v___x_4769_ = v___x_4763_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_stream_4755_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_nameMap_4756_);
lean_ctor_set(v_reuseFailAlloc_4776_, 2, v_levelMap_4757_);
lean_ctor_set(v_reuseFailAlloc_4776_, 3, v___x_4767_);
lean_ctor_set(v_reuseFailAlloc_4776_, 4, v_recursorRuleMap_4759_);
lean_ctor_set(v_reuseFailAlloc_4776_, 5, v_constMap_4760_);
lean_ctor_set(v_reuseFailAlloc_4776_, 6, v_constOrder_4761_);
v___x_4769_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4771_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 1, v___x_4769_);
lean_ctor_set(v___x_4753_, 0, v___x_4766_);
v___x_4771_ = v___x_4753_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v___x_4769_);
v___x_4771_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4771_);
v___x_4773_ = v___x_4748_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
lean_del_object(v___x_4763_);
lean_dec_ref(v_constOrder_4761_);
lean_dec_ref(v_constMap_4760_);
lean_dec_ref(v_recursorRuleMap_4759_);
lean_dec_ref(v_exprMap_4758_);
lean_dec_ref(v_levelMap_4757_);
lean_dec_ref(v_nameMap_4756_);
lean_dec_ref(v_stream_4755_);
lean_del_object(v___x_4753_);
lean_dec(v_fst_4751_);
v___x_4777_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4778_ = l_Nat_reprFast(v_a_4506_);
v___x_4779_ = lean_string_append(v___x_4777_, v___x_4778_);
lean_dec_ref(v___x_4778_);
v___x_4780_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4781_ = lean_string_append(v___x_4779_, v___x_4780_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4781_);
v___x_4783_ = v___x_4494_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4785_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set_tag(v___x_4748_, 1);
lean_ctor_set(v___x_4748_, 0, v___x_4783_);
v___x_4785_ = v___x_4748_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4791_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4745_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4745_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4799_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4799_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4844_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4844_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4844_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_snd_4804_; lean_object* v_fst_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4843_; 
v_snd_4804_ = lean_ctor_get(v_a_4800_, 1);
v_fst_4805_ = lean_ctor_get(v_a_4800_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_a_4800_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4807_ = v_a_4800_;
v_isShared_4808_ = v_isSharedCheck_4843_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_snd_4804_);
lean_inc(v_fst_4805_);
lean_dec(v_a_4800_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4843_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v_stream_4809_; lean_object* v_nameMap_4810_; lean_object* v_levelMap_4811_; lean_object* v_exprMap_4812_; lean_object* v_recursorRuleMap_4813_; lean_object* v_constMap_4814_; lean_object* v_constOrder_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4842_; 
v_stream_4809_ = lean_ctor_get(v_snd_4804_, 0);
v_nameMap_4810_ = lean_ctor_get(v_snd_4804_, 1);
v_levelMap_4811_ = lean_ctor_get(v_snd_4804_, 2);
v_exprMap_4812_ = lean_ctor_get(v_snd_4804_, 3);
v_recursorRuleMap_4813_ = lean_ctor_get(v_snd_4804_, 4);
v_constMap_4814_ = lean_ctor_get(v_snd_4804_, 5);
v_constOrder_4815_ = lean_ctor_get(v_snd_4804_, 6);
v_isSharedCheck_4842_ = !lean_is_exclusive(v_snd_4804_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4817_ = v_snd_4804_;
v_isShared_4818_ = v_isSharedCheck_4842_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_constOrder_4815_);
lean_inc(v_constMap_4814_);
lean_inc(v_recursorRuleMap_4813_);
lean_inc(v_exprMap_4812_);
lean_inc(v_levelMap_4811_);
lean_inc(v_nameMap_4810_);
lean_inc(v_stream_4809_);
lean_dec(v_snd_4804_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4842_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
uint8_t v___x_4819_; 
v___x_4819_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4812_, v_a_4506_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
lean_del_object(v___x_4494_);
v___x_4820_ = lean_box(0);
v___x_4821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4812_, v_a_4506_, v_fst_4805_);
if (v_isShared_4818_ == 0)
{
lean_ctor_set(v___x_4817_, 3, v___x_4821_);
v___x_4823_ = v___x_4817_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_stream_4809_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_nameMap_4810_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_levelMap_4811_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_recursorRuleMap_4813_);
lean_ctor_set(v_reuseFailAlloc_4830_, 5, v_constMap_4814_);
lean_ctor_set(v_reuseFailAlloc_4830_, 6, v_constOrder_4815_);
v___x_4823_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
lean_object* v___x_4825_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 1, v___x_4823_);
lean_ctor_set(v___x_4807_, 0, v___x_4820_);
v___x_4825_ = v___x_4807_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
lean_object* v___x_4827_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4825_);
v___x_4827_ = v___x_4802_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
lean_del_object(v___x_4817_);
lean_dec_ref(v_constOrder_4815_);
lean_dec_ref(v_constMap_4814_);
lean_dec_ref(v_recursorRuleMap_4813_);
lean_dec_ref(v_exprMap_4812_);
lean_dec_ref(v_levelMap_4811_);
lean_dec_ref(v_nameMap_4810_);
lean_dec_ref(v_stream_4809_);
lean_del_object(v___x_4807_);
lean_dec(v_fst_4805_);
v___x_4831_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4832_ = l_Nat_reprFast(v_a_4506_);
v___x_4833_ = lean_string_append(v___x_4831_, v___x_4832_);
lean_dec_ref(v___x_4832_);
v___x_4834_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4835_ = lean_string_append(v___x_4833_, v___x_4834_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4835_);
v___x_4837_ = v___x_4494_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4835_);
v___x_4837_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4839_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set_tag(v___x_4802_, 1);
lean_ctor_set(v___x_4802_, 0, v___x_4837_);
v___x_4839_ = v___x_4802_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4837_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4845_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4799_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4799_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4853_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4853_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4898_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4856_ = v___x_4853_;
v_isShared_4857_ = v_isSharedCheck_4898_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4853_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4898_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v_snd_4858_; lean_object* v_fst_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4897_; 
v_snd_4858_ = lean_ctor_get(v_a_4854_, 1);
v_fst_4859_ = lean_ctor_get(v_a_4854_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_a_4854_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4861_ = v_a_4854_;
v_isShared_4862_ = v_isSharedCheck_4897_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_snd_4858_);
lean_inc(v_fst_4859_);
lean_dec(v_a_4854_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4897_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v_stream_4863_; lean_object* v_nameMap_4864_; lean_object* v_levelMap_4865_; lean_object* v_exprMap_4866_; lean_object* v_recursorRuleMap_4867_; lean_object* v_constMap_4868_; lean_object* v_constOrder_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4896_; 
v_stream_4863_ = lean_ctor_get(v_snd_4858_, 0);
v_nameMap_4864_ = lean_ctor_get(v_snd_4858_, 1);
v_levelMap_4865_ = lean_ctor_get(v_snd_4858_, 2);
v_exprMap_4866_ = lean_ctor_get(v_snd_4858_, 3);
v_recursorRuleMap_4867_ = lean_ctor_get(v_snd_4858_, 4);
v_constMap_4868_ = lean_ctor_get(v_snd_4858_, 5);
v_constOrder_4869_ = lean_ctor_get(v_snd_4858_, 6);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_snd_4858_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4871_ = v_snd_4858_;
v_isShared_4872_ = v_isSharedCheck_4896_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_constOrder_4869_);
lean_inc(v_constMap_4868_);
lean_inc(v_recursorRuleMap_4867_);
lean_inc(v_exprMap_4866_);
lean_inc(v_levelMap_4865_);
lean_inc(v_nameMap_4864_);
lean_inc(v_stream_4863_);
lean_dec(v_snd_4858_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4896_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
uint8_t v___x_4873_; 
v___x_4873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4866_, v_a_4506_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4877_; 
lean_del_object(v___x_4494_);
v___x_4874_ = lean_box(0);
v___x_4875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4866_, v_a_4506_, v_fst_4859_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 3, v___x_4875_);
v___x_4877_ = v___x_4871_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_stream_4863_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_nameMap_4864_);
lean_ctor_set(v_reuseFailAlloc_4884_, 2, v_levelMap_4865_);
lean_ctor_set(v_reuseFailAlloc_4884_, 3, v___x_4875_);
lean_ctor_set(v_reuseFailAlloc_4884_, 4, v_recursorRuleMap_4867_);
lean_ctor_set(v_reuseFailAlloc_4884_, 5, v_constMap_4868_);
lean_ctor_set(v_reuseFailAlloc_4884_, 6, v_constOrder_4869_);
v___x_4877_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
lean_object* v___x_4879_; 
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 1, v___x_4877_);
lean_ctor_set(v___x_4861_, 0, v___x_4874_);
v___x_4879_ = v___x_4861_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4883_, 1, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
lean_object* v___x_4881_; 
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4879_);
v___x_4881_ = v___x_4856_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
lean_del_object(v___x_4871_);
lean_dec_ref(v_constOrder_4869_);
lean_dec_ref(v_constMap_4868_);
lean_dec_ref(v_recursorRuleMap_4867_);
lean_dec_ref(v_exprMap_4866_);
lean_dec_ref(v_levelMap_4865_);
lean_dec_ref(v_nameMap_4864_);
lean_dec_ref(v_stream_4863_);
lean_del_object(v___x_4861_);
lean_dec(v_fst_4859_);
v___x_4885_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4886_ = l_Nat_reprFast(v_a_4506_);
v___x_4887_ = lean_string_append(v___x_4885_, v___x_4886_);
lean_dec_ref(v___x_4886_);
v___x_4888_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4889_ = lean_string_append(v___x_4887_, v___x_4888_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4889_);
v___x_4891_ = v___x_4494_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4893_; 
if (v_isShared_4857_ == 0)
{
lean_ctor_set_tag(v___x_4856_, 1);
lean_ctor_set(v___x_4856_, 0, v___x_4891_);
v___x_4893_ = v___x_4856_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4899_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4853_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4853_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4907_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4907_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4952_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4910_ = v___x_4907_;
v_isShared_4911_ = v_isSharedCheck_4952_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4907_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4952_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v_snd_4912_; lean_object* v_fst_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4951_; 
v_snd_4912_ = lean_ctor_get(v_a_4908_, 1);
v_fst_4913_ = lean_ctor_get(v_a_4908_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_a_4908_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4915_ = v_a_4908_;
v_isShared_4916_ = v_isSharedCheck_4951_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_snd_4912_);
lean_inc(v_fst_4913_);
lean_dec(v_a_4908_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4951_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v_stream_4917_; lean_object* v_nameMap_4918_; lean_object* v_levelMap_4919_; lean_object* v_exprMap_4920_; lean_object* v_recursorRuleMap_4921_; lean_object* v_constMap_4922_; lean_object* v_constOrder_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4950_; 
v_stream_4917_ = lean_ctor_get(v_snd_4912_, 0);
v_nameMap_4918_ = lean_ctor_get(v_snd_4912_, 1);
v_levelMap_4919_ = lean_ctor_get(v_snd_4912_, 2);
v_exprMap_4920_ = lean_ctor_get(v_snd_4912_, 3);
v_recursorRuleMap_4921_ = lean_ctor_get(v_snd_4912_, 4);
v_constMap_4922_ = lean_ctor_get(v_snd_4912_, 5);
v_constOrder_4923_ = lean_ctor_get(v_snd_4912_, 6);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_snd_4912_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4925_ = v_snd_4912_;
v_isShared_4926_ = v_isSharedCheck_4950_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_constOrder_4923_);
lean_inc(v_constMap_4922_);
lean_inc(v_recursorRuleMap_4921_);
lean_inc(v_exprMap_4920_);
lean_inc(v_levelMap_4919_);
lean_inc(v_nameMap_4918_);
lean_inc(v_stream_4917_);
lean_dec(v_snd_4912_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4950_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
uint8_t v___x_4927_; 
v___x_4927_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4920_, v_a_4506_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
lean_del_object(v___x_4494_);
v___x_4928_ = lean_box(0);
v___x_4929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4920_, v_a_4506_, v_fst_4913_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 3, v___x_4929_);
v___x_4931_ = v___x_4925_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_stream_4917_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_nameMap_4918_);
lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_levelMap_4919_);
lean_ctor_set(v_reuseFailAlloc_4938_, 3, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4938_, 4, v_recursorRuleMap_4921_);
lean_ctor_set(v_reuseFailAlloc_4938_, 5, v_constMap_4922_);
lean_ctor_set(v_reuseFailAlloc_4938_, 6, v_constOrder_4923_);
v___x_4931_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4933_; 
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 1, v___x_4931_);
lean_ctor_set(v___x_4915_, 0, v___x_4928_);
v___x_4933_ = v___x_4915_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4933_);
v___x_4935_ = v___x_4910_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
else
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
lean_del_object(v___x_4925_);
lean_dec_ref(v_constOrder_4923_);
lean_dec_ref(v_constMap_4922_);
lean_dec_ref(v_recursorRuleMap_4921_);
lean_dec_ref(v_exprMap_4920_);
lean_dec_ref(v_levelMap_4919_);
lean_dec_ref(v_nameMap_4918_);
lean_dec_ref(v_stream_4917_);
lean_del_object(v___x_4915_);
lean_dec(v_fst_4913_);
v___x_4939_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4940_ = l_Nat_reprFast(v_a_4506_);
v___x_4941_ = lean_string_append(v___x_4939_, v___x_4940_);
lean_dec_ref(v___x_4940_);
v___x_4942_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4943_ = lean_string_append(v___x_4941_, v___x_4942_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4943_);
v___x_4945_ = v___x_4494_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4943_);
v___x_4945_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4947_; 
if (v_isShared_4911_ == 0)
{
lean_ctor_set_tag(v___x_4910_, 1);
lean_ctor_set(v___x_4910_, 0, v___x_4945_);
v___x_4947_ = v___x_4910_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_4953_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4907_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4907_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_4961_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_4961_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_snd_4505_, v_a_4424_);
lean_dec(v_snd_4505_);
if (lean_obj_tag(v___x_4961_) == 0)
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_5006_; 
v_a_4962_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4964_ = v___x_4961_;
v_isShared_4965_ = v_isSharedCheck_5006_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4961_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_5006_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v_snd_4966_; lean_object* v_fst_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5005_; 
v_snd_4966_ = lean_ctor_get(v_a_4962_, 1);
v_fst_4967_ = lean_ctor_get(v_a_4962_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v_a_4962_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4969_ = v_a_4962_;
v_isShared_4970_ = v_isSharedCheck_5005_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_snd_4966_);
lean_inc(v_fst_4967_);
lean_dec(v_a_4962_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5005_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v_stream_4971_; lean_object* v_nameMap_4972_; lean_object* v_levelMap_4973_; lean_object* v_exprMap_4974_; lean_object* v_recursorRuleMap_4975_; lean_object* v_constMap_4976_; lean_object* v_constOrder_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_5004_; 
v_stream_4971_ = lean_ctor_get(v_snd_4966_, 0);
v_nameMap_4972_ = lean_ctor_get(v_snd_4966_, 1);
v_levelMap_4973_ = lean_ctor_get(v_snd_4966_, 2);
v_exprMap_4974_ = lean_ctor_get(v_snd_4966_, 3);
v_recursorRuleMap_4975_ = lean_ctor_get(v_snd_4966_, 4);
v_constMap_4976_ = lean_ctor_get(v_snd_4966_, 5);
v_constOrder_4977_ = lean_ctor_get(v_snd_4966_, 6);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_snd_4966_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4979_ = v_snd_4966_;
v_isShared_4980_ = v_isSharedCheck_5004_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_constOrder_4977_);
lean_inc(v_constMap_4976_);
lean_inc(v_recursorRuleMap_4975_);
lean_inc(v_exprMap_4974_);
lean_inc(v_levelMap_4973_);
lean_inc(v_nameMap_4972_);
lean_inc(v_stream_4971_);
lean_dec(v_snd_4966_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_5004_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
uint8_t v___x_4981_; 
v___x_4981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4974_, v_a_4506_);
if (v___x_4981_ == 0)
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4985_; 
lean_del_object(v___x_4494_);
v___x_4982_ = lean_box(0);
v___x_4983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4974_, v_a_4506_, v_fst_4967_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 3, v___x_4983_);
v___x_4985_ = v___x_4979_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_stream_4971_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_nameMap_4972_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_levelMap_4973_);
lean_ctor_set(v_reuseFailAlloc_4992_, 3, v___x_4983_);
lean_ctor_set(v_reuseFailAlloc_4992_, 4, v_recursorRuleMap_4975_);
lean_ctor_set(v_reuseFailAlloc_4992_, 5, v_constMap_4976_);
lean_ctor_set(v_reuseFailAlloc_4992_, 6, v_constOrder_4977_);
v___x_4985_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 1, v___x_4985_);
lean_ctor_set(v___x_4969_, 0, v___x_4982_);
v___x_4987_ = v___x_4969_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4989_; 
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 0, v___x_4987_);
v___x_4989_ = v___x_4964_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
else
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4999_; 
lean_del_object(v___x_4979_);
lean_dec_ref(v_constOrder_4977_);
lean_dec_ref(v_constMap_4976_);
lean_dec_ref(v_recursorRuleMap_4975_);
lean_dec_ref(v_exprMap_4974_);
lean_dec_ref(v_levelMap_4973_);
lean_dec_ref(v_nameMap_4972_);
lean_dec_ref(v_stream_4971_);
lean_del_object(v___x_4969_);
lean_dec(v_fst_4967_);
v___x_4993_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4994_ = l_Nat_reprFast(v_a_4506_);
v___x_4995_ = lean_string_append(v___x_4993_, v___x_4994_);
lean_dec_ref(v___x_4994_);
v___x_4996_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4997_ = lean_string_append(v___x_4995_, v___x_4996_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_4997_);
v___x_4999_ = v___x_4494_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5003_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5001_; 
if (v_isShared_4965_ == 0)
{
lean_ctor_set_tag(v___x_4964_, 1);
lean_ctor_set(v___x_4964_, 0, v___x_4999_);
v___x_5001_ = v___x_4964_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v___x_4999_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_5007_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4961_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4961_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_5015_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5015_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_snd_4505_, v_a_4424_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5060_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5018_ = v___x_5015_;
v_isShared_5019_ = v_isSharedCheck_5060_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5060_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v_snd_5020_; lean_object* v_fst_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5059_; 
v_snd_5020_ = lean_ctor_get(v_a_5016_, 1);
v_fst_5021_ = lean_ctor_get(v_a_5016_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v_a_5016_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5023_ = v_a_5016_;
v_isShared_5024_ = v_isSharedCheck_5059_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_snd_5020_);
lean_inc(v_fst_5021_);
lean_dec(v_a_5016_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5059_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v_stream_5025_; lean_object* v_nameMap_5026_; lean_object* v_levelMap_5027_; lean_object* v_exprMap_5028_; lean_object* v_recursorRuleMap_5029_; lean_object* v_constMap_5030_; lean_object* v_constOrder_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5058_; 
v_stream_5025_ = lean_ctor_get(v_snd_5020_, 0);
v_nameMap_5026_ = lean_ctor_get(v_snd_5020_, 1);
v_levelMap_5027_ = lean_ctor_get(v_snd_5020_, 2);
v_exprMap_5028_ = lean_ctor_get(v_snd_5020_, 3);
v_recursorRuleMap_5029_ = lean_ctor_get(v_snd_5020_, 4);
v_constMap_5030_ = lean_ctor_get(v_snd_5020_, 5);
v_constOrder_5031_ = lean_ctor_get(v_snd_5020_, 6);
v_isSharedCheck_5058_ = !lean_is_exclusive(v_snd_5020_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5033_ = v_snd_5020_;
v_isShared_5034_ = v_isSharedCheck_5058_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_constOrder_5031_);
lean_inc(v_constMap_5030_);
lean_inc(v_recursorRuleMap_5029_);
lean_inc(v_exprMap_5028_);
lean_inc(v_levelMap_5027_);
lean_inc(v_nameMap_5026_);
lean_inc(v_stream_5025_);
lean_dec(v_snd_5020_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5058_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
uint8_t v___x_5035_; 
v___x_5035_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_5028_, v_a_4506_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5039_; 
lean_del_object(v___x_4494_);
v___x_5036_ = lean_box(0);
v___x_5037_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_5028_, v_a_4506_, v_fst_5021_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 3, v___x_5037_);
v___x_5039_ = v___x_5033_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_stream_5025_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v_nameMap_5026_);
lean_ctor_set(v_reuseFailAlloc_5046_, 2, v_levelMap_5027_);
lean_ctor_set(v_reuseFailAlloc_5046_, 3, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5046_, 4, v_recursorRuleMap_5029_);
lean_ctor_set(v_reuseFailAlloc_5046_, 5, v_constMap_5030_);
lean_ctor_set(v_reuseFailAlloc_5046_, 6, v_constOrder_5031_);
v___x_5039_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
lean_object* v___x_5041_; 
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 1, v___x_5039_);
lean_ctor_set(v___x_5023_, 0, v___x_5036_);
v___x_5041_ = v___x_5023_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5036_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v___x_5039_);
v___x_5041_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5043_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 0, v___x_5041_);
v___x_5043_ = v___x_5018_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5053_; 
lean_del_object(v___x_5033_);
lean_dec_ref(v_constOrder_5031_);
lean_dec_ref(v_constMap_5030_);
lean_dec_ref(v_recursorRuleMap_5029_);
lean_dec_ref(v_exprMap_5028_);
lean_dec_ref(v_levelMap_5027_);
lean_dec_ref(v_nameMap_5026_);
lean_dec_ref(v_stream_5025_);
lean_del_object(v___x_5023_);
lean_dec(v_fst_5021_);
v___x_5047_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_5048_ = l_Nat_reprFast(v_a_4506_);
v___x_5049_ = lean_string_append(v___x_5047_, v___x_5048_);
lean_dec_ref(v___x_5048_);
v___x_5050_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5051_ = lean_string_append(v___x_5049_, v___x_5050_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_5051_);
v___x_5053_ = v___x_4494_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
lean_object* v___x_5055_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set_tag(v___x_5018_, 1);
lean_ctor_set(v___x_5018_, 0, v___x_5053_);
v___x_5055_ = v___x_5018_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_5061_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5015_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5015_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_4504_);
if (lean_obj_tag(v_tail_4503_) == 0)
{
lean_object* v___x_5069_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5069_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_snd_4505_, v_a_4424_);
if (lean_obj_tag(v___x_5069_) == 0)
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5114_; 
v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5072_ = v___x_5069_;
v_isShared_5073_ = v_isSharedCheck_5114_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5069_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5114_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v_snd_5074_; lean_object* v_fst_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5113_; 
v_snd_5074_ = lean_ctor_get(v_a_5070_, 1);
v_fst_5075_ = lean_ctor_get(v_a_5070_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v_a_5070_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5077_ = v_a_5070_;
v_isShared_5078_ = v_isSharedCheck_5113_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_snd_5074_);
lean_inc(v_fst_5075_);
lean_dec(v_a_5070_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5113_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v_stream_5079_; lean_object* v_nameMap_5080_; lean_object* v_levelMap_5081_; lean_object* v_exprMap_5082_; lean_object* v_recursorRuleMap_5083_; lean_object* v_constMap_5084_; lean_object* v_constOrder_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5112_; 
v_stream_5079_ = lean_ctor_get(v_snd_5074_, 0);
v_nameMap_5080_ = lean_ctor_get(v_snd_5074_, 1);
v_levelMap_5081_ = lean_ctor_get(v_snd_5074_, 2);
v_exprMap_5082_ = lean_ctor_get(v_snd_5074_, 3);
v_recursorRuleMap_5083_ = lean_ctor_get(v_snd_5074_, 4);
v_constMap_5084_ = lean_ctor_get(v_snd_5074_, 5);
v_constOrder_5085_ = lean_ctor_get(v_snd_5074_, 6);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_snd_5074_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5087_ = v_snd_5074_;
v_isShared_5088_ = v_isSharedCheck_5112_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_constOrder_5085_);
lean_inc(v_constMap_5084_);
lean_inc(v_recursorRuleMap_5083_);
lean_inc(v_exprMap_5082_);
lean_inc(v_levelMap_5081_);
lean_inc(v_nameMap_5080_);
lean_inc(v_stream_5079_);
lean_dec(v_snd_5074_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5112_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
uint8_t v___x_5089_; 
v___x_5089_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_5082_, v_a_4506_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5093_; 
lean_del_object(v___x_4494_);
v___x_5090_ = lean_box(0);
v___x_5091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_5082_, v_a_4506_, v_fst_5075_);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 3, v___x_5091_);
v___x_5093_ = v___x_5087_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_stream_5079_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_nameMap_5080_);
lean_ctor_set(v_reuseFailAlloc_5100_, 2, v_levelMap_5081_);
lean_ctor_set(v_reuseFailAlloc_5100_, 3, v___x_5091_);
lean_ctor_set(v_reuseFailAlloc_5100_, 4, v_recursorRuleMap_5083_);
lean_ctor_set(v_reuseFailAlloc_5100_, 5, v_constMap_5084_);
lean_ctor_set(v_reuseFailAlloc_5100_, 6, v_constOrder_5085_);
v___x_5093_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5095_; 
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 1, v___x_5093_);
lean_ctor_set(v___x_5077_, 0, v___x_5090_);
v___x_5095_ = v___x_5077_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5090_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5093_);
v___x_5095_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
lean_object* v___x_5097_; 
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 0, v___x_5095_);
v___x_5097_ = v___x_5072_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5095_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5107_; 
lean_del_object(v___x_5087_);
lean_dec_ref(v_constOrder_5085_);
lean_dec_ref(v_constMap_5084_);
lean_dec_ref(v_recursorRuleMap_5083_);
lean_dec_ref(v_exprMap_5082_);
lean_dec_ref(v_levelMap_5081_);
lean_dec_ref(v_nameMap_5080_);
lean_dec_ref(v_stream_5079_);
lean_del_object(v___x_5077_);
lean_dec(v_fst_5075_);
v___x_5101_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_5102_ = l_Nat_reprFast(v_a_4506_);
v___x_5103_ = lean_string_append(v___x_5101_, v___x_5102_);
lean_dec_ref(v___x_5102_);
v___x_5104_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5105_ = lean_string_append(v___x_5103_, v___x_5104_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 18);
lean_ctor_set(v___x_4494_, 0, v___x_5105_);
v___x_5107_ = v___x_4494_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_5073_ == 0)
{
lean_ctor_set_tag(v___x_5072_, 1);
lean_ctor_set(v___x_5072_, 0, v___x_5107_);
v___x_5109_ = v___x_5072_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec(v_a_4506_);
lean_del_object(v___x_4494_);
v_a_5115_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5069_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5069_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_snd_4505_);
lean_dec(v_tail_4503_);
lean_del_object(v___x_4494_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_mantissa_4496_);
lean_del_object(v___x_4494_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_exponent_4497_);
lean_dec(v_mantissa_4496_);
lean_del_object(v___x_4494_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 2)
{
lean_object* v_n_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5363_; 
v_n_5124_ = lean_ctor_get(v_snd_4460_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v_snd_4460_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5126_ = v_snd_4460_;
v_isShared_5127_ = v_isSharedCheck_5363_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_n_5124_);
lean_dec(v_snd_4460_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5363_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v_mantissa_5128_; lean_object* v_exponent_5129_; lean_object* v_natZero_5130_; lean_object* v_intZero_5131_; uint8_t v_isNeg_5132_; 
v_mantissa_5128_ = lean_ctor_get(v_n_5124_, 0);
lean_inc(v_mantissa_5128_);
v_exponent_5129_ = lean_ctor_get(v_n_5124_, 1);
lean_inc(v_exponent_5129_);
lean_dec_ref(v_n_5124_);
v_natZero_5130_ = lean_unsigned_to_nat(0u);
v_intZero_5131_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5132_ = lean_int_dec_lt(v_mantissa_5128_, v_intZero_5131_);
if (v_isNeg_5132_ == 0)
{
uint8_t v___x_5133_; 
v___x_5133_ = lean_nat_dec_eq(v_exponent_5129_, v_natZero_5130_);
lean_dec(v_exponent_5129_);
if (v___x_5133_ == 0)
{
lean_dec(v_mantissa_5128_);
lean_del_object(v___x_5126_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_4461_) == 1)
{
lean_object* v_head_5134_; lean_object* v_tail_5135_; lean_object* v_fst_5136_; lean_object* v_snd_5137_; lean_object* v_a_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
v_head_5134_ = lean_ctor_get(v_tail_4461_, 0);
lean_inc(v_head_5134_);
v_tail_5135_ = lean_ctor_get(v_tail_4461_, 1);
lean_inc(v_tail_5135_);
lean_dec_ref_known(v_tail_4461_, 2);
v_fst_5136_ = lean_ctor_get(v_head_5134_, 0);
lean_inc(v_fst_5136_);
v_snd_5137_ = lean_ctor_get(v_head_5134_, 1);
lean_inc(v_snd_5137_);
lean_dec(v_head_5134_);
v_a_5138_ = lean_nat_abs(v_mantissa_5128_);
lean_dec(v_mantissa_5128_);
v___x_5139_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20));
v___x_5140_ = lean_string_dec_eq(v_fst_5136_, v___x_5139_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; uint8_t v___x_5142_; 
v___x_5141_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21));
v___x_5142_ = lean_string_dec_eq(v_fst_5136_, v___x_5141_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; uint8_t v___x_5144_; 
v___x_5143_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22));
v___x_5144_ = lean_string_dec_eq(v_fst_5136_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; uint8_t v___x_5146_; 
v___x_5145_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23));
v___x_5146_ = lean_string_dec_eq(v_fst_5136_, v___x_5145_);
lean_dec(v_fst_5136_);
if (v___x_5146_ == 0)
{
lean_dec(v_a_5138_);
lean_dec(v_snd_5137_);
lean_dec(v_tail_5135_);
lean_del_object(v___x_5126_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_5135_) == 0)
{
lean_object* v___x_5147_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5147_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_snd_5137_, v_a_4424_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5192_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5150_ = v___x_5147_;
v_isShared_5151_ = v_isSharedCheck_5192_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5147_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5192_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v_snd_5152_; lean_object* v_fst_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5191_; 
v_snd_5152_ = lean_ctor_get(v_a_5148_, 1);
v_fst_5153_ = lean_ctor_get(v_a_5148_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v_a_5148_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5155_ = v_a_5148_;
v_isShared_5156_ = v_isSharedCheck_5191_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_snd_5152_);
lean_inc(v_fst_5153_);
lean_dec(v_a_5148_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5191_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v_stream_5157_; lean_object* v_nameMap_5158_; lean_object* v_levelMap_5159_; lean_object* v_exprMap_5160_; lean_object* v_recursorRuleMap_5161_; lean_object* v_constMap_5162_; lean_object* v_constOrder_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5190_; 
v_stream_5157_ = lean_ctor_get(v_snd_5152_, 0);
v_nameMap_5158_ = lean_ctor_get(v_snd_5152_, 1);
v_levelMap_5159_ = lean_ctor_get(v_snd_5152_, 2);
v_exprMap_5160_ = lean_ctor_get(v_snd_5152_, 3);
v_recursorRuleMap_5161_ = lean_ctor_get(v_snd_5152_, 4);
v_constMap_5162_ = lean_ctor_get(v_snd_5152_, 5);
v_constOrder_5163_ = lean_ctor_get(v_snd_5152_, 6);
v_isSharedCheck_5190_ = !lean_is_exclusive(v_snd_5152_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5165_ = v_snd_5152_;
v_isShared_5166_ = v_isSharedCheck_5190_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_constOrder_5163_);
lean_inc(v_constMap_5162_);
lean_inc(v_recursorRuleMap_5161_);
lean_inc(v_exprMap_5160_);
lean_inc(v_levelMap_5159_);
lean_inc(v_nameMap_5158_);
lean_inc(v_stream_5157_);
lean_dec(v_snd_5152_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5190_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
uint8_t v___x_5167_; 
v___x_5167_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5159_, v_a_5138_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5171_; 
lean_del_object(v___x_5126_);
v___x_5168_ = lean_box(0);
v___x_5169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5159_, v_a_5138_, v_fst_5153_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 2, v___x_5169_);
v___x_5171_ = v___x_5165_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_stream_5157_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v_nameMap_5158_);
lean_ctor_set(v_reuseFailAlloc_5178_, 2, v___x_5169_);
lean_ctor_set(v_reuseFailAlloc_5178_, 3, v_exprMap_5160_);
lean_ctor_set(v_reuseFailAlloc_5178_, 4, v_recursorRuleMap_5161_);
lean_ctor_set(v_reuseFailAlloc_5178_, 5, v_constMap_5162_);
lean_ctor_set(v_reuseFailAlloc_5178_, 6, v_constOrder_5163_);
v___x_5171_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
lean_object* v___x_5173_; 
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 1, v___x_5171_);
lean_ctor_set(v___x_5155_, 0, v___x_5168_);
v___x_5173_ = v___x_5155_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5168_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5175_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 0, v___x_5173_);
v___x_5175_ = v___x_5150_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5173_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5185_; 
lean_del_object(v___x_5165_);
lean_dec_ref(v_constOrder_5163_);
lean_dec_ref(v_constMap_5162_);
lean_dec_ref(v_recursorRuleMap_5161_);
lean_dec_ref(v_exprMap_5160_);
lean_dec_ref(v_levelMap_5159_);
lean_dec_ref(v_nameMap_5158_);
lean_dec_ref(v_stream_5157_);
lean_del_object(v___x_5155_);
lean_dec(v_fst_5153_);
v___x_5179_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5180_ = l_Nat_reprFast(v_a_5138_);
v___x_5181_ = lean_string_append(v___x_5179_, v___x_5180_);
lean_dec_ref(v___x_5180_);
v___x_5182_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5183_ = lean_string_append(v___x_5181_, v___x_5182_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 18);
lean_ctor_set(v___x_5126_, 0, v___x_5183_);
v___x_5185_ = v___x_5126_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5187_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set_tag(v___x_5150_, 1);
lean_ctor_set(v___x_5150_, 0, v___x_5185_);
v___x_5187_ = v___x_5150_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec(v_a_5138_);
lean_del_object(v___x_5126_);
v_a_5193_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5147_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5147_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_dec(v_a_5138_);
lean_dec(v_snd_5137_);
lean_dec(v_tail_5135_);
lean_del_object(v___x_5126_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_5136_);
if (lean_obj_tag(v_tail_5135_) == 0)
{
lean_object* v___x_5201_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5201_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_snd_5137_, v_a_4424_);
lean_dec(v_snd_5137_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5246_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5204_ = v___x_5201_;
v_isShared_5205_ = v_isSharedCheck_5246_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5246_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v_snd_5206_; lean_object* v_fst_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5245_; 
v_snd_5206_ = lean_ctor_get(v_a_5202_, 1);
v_fst_5207_ = lean_ctor_get(v_a_5202_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v_a_5202_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5209_ = v_a_5202_;
v_isShared_5210_ = v_isSharedCheck_5245_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_snd_5206_);
lean_inc(v_fst_5207_);
lean_dec(v_a_5202_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5245_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v_stream_5211_; lean_object* v_nameMap_5212_; lean_object* v_levelMap_5213_; lean_object* v_exprMap_5214_; lean_object* v_recursorRuleMap_5215_; lean_object* v_constMap_5216_; lean_object* v_constOrder_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5244_; 
v_stream_5211_ = lean_ctor_get(v_snd_5206_, 0);
v_nameMap_5212_ = lean_ctor_get(v_snd_5206_, 1);
v_levelMap_5213_ = lean_ctor_get(v_snd_5206_, 2);
v_exprMap_5214_ = lean_ctor_get(v_snd_5206_, 3);
v_recursorRuleMap_5215_ = lean_ctor_get(v_snd_5206_, 4);
v_constMap_5216_ = lean_ctor_get(v_snd_5206_, 5);
v_constOrder_5217_ = lean_ctor_get(v_snd_5206_, 6);
v_isSharedCheck_5244_ = !lean_is_exclusive(v_snd_5206_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5219_ = v_snd_5206_;
v_isShared_5220_ = v_isSharedCheck_5244_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_constOrder_5217_);
lean_inc(v_constMap_5216_);
lean_inc(v_recursorRuleMap_5215_);
lean_inc(v_exprMap_5214_);
lean_inc(v_levelMap_5213_);
lean_inc(v_nameMap_5212_);
lean_inc(v_stream_5211_);
lean_dec(v_snd_5206_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5244_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
uint8_t v___x_5221_; 
v___x_5221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5213_, v_a_5138_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5225_; 
lean_del_object(v___x_5126_);
v___x_5222_ = lean_box(0);
v___x_5223_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5213_, v_a_5138_, v_fst_5207_);
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 2, v___x_5223_);
v___x_5225_ = v___x_5219_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_stream_5211_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v_nameMap_5212_);
lean_ctor_set(v_reuseFailAlloc_5232_, 2, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5232_, 3, v_exprMap_5214_);
lean_ctor_set(v_reuseFailAlloc_5232_, 4, v_recursorRuleMap_5215_);
lean_ctor_set(v_reuseFailAlloc_5232_, 5, v_constMap_5216_);
lean_ctor_set(v_reuseFailAlloc_5232_, 6, v_constOrder_5217_);
v___x_5225_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5227_; 
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 1, v___x_5225_);
lean_ctor_set(v___x_5209_, 0, v___x_5222_);
v___x_5227_ = v___x_5209_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5231_, 1, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5229_; 
if (v_isShared_5205_ == 0)
{
lean_ctor_set(v___x_5204_, 0, v___x_5227_);
v___x_5229_ = v___x_5204_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5239_; 
lean_del_object(v___x_5219_);
lean_dec_ref(v_constOrder_5217_);
lean_dec_ref(v_constMap_5216_);
lean_dec_ref(v_recursorRuleMap_5215_);
lean_dec_ref(v_exprMap_5214_);
lean_dec_ref(v_levelMap_5213_);
lean_dec_ref(v_nameMap_5212_);
lean_dec_ref(v_stream_5211_);
lean_del_object(v___x_5209_);
lean_dec(v_fst_5207_);
v___x_5233_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5234_ = l_Nat_reprFast(v_a_5138_);
v___x_5235_ = lean_string_append(v___x_5233_, v___x_5234_);
lean_dec_ref(v___x_5234_);
v___x_5236_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5237_ = lean_string_append(v___x_5235_, v___x_5236_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 18);
lean_ctor_set(v___x_5126_, 0, v___x_5237_);
v___x_5239_ = v___x_5126_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5237_);
v___x_5239_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5241_; 
if (v_isShared_5205_ == 0)
{
lean_ctor_set_tag(v___x_5204_, 1);
lean_ctor_set(v___x_5204_, 0, v___x_5239_);
v___x_5241_ = v___x_5204_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_dec(v_a_5138_);
lean_del_object(v___x_5126_);
v_a_5247_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5201_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5201_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
else
{
lean_dec(v_a_5138_);
lean_dec(v_snd_5137_);
lean_dec(v_tail_5135_);
lean_del_object(v___x_5126_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_5136_);
if (lean_obj_tag(v_tail_5135_) == 0)
{
lean_object* v___x_5255_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5255_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_snd_5137_, v_a_4424_);
lean_dec(v_snd_5137_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5300_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5300_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5300_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v_snd_5260_; lean_object* v_fst_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5299_; 
v_snd_5260_ = lean_ctor_get(v_a_5256_, 1);
v_fst_5261_ = lean_ctor_get(v_a_5256_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v_a_5256_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5263_ = v_a_5256_;
v_isShared_5264_ = v_isSharedCheck_5299_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_snd_5260_);
lean_inc(v_fst_5261_);
lean_dec(v_a_5256_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5299_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v_stream_5265_; lean_object* v_nameMap_5266_; lean_object* v_levelMap_5267_; lean_object* v_exprMap_5268_; lean_object* v_recursorRuleMap_5269_; lean_object* v_constMap_5270_; lean_object* v_constOrder_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5298_; 
v_stream_5265_ = lean_ctor_get(v_snd_5260_, 0);
v_nameMap_5266_ = lean_ctor_get(v_snd_5260_, 1);
v_levelMap_5267_ = lean_ctor_get(v_snd_5260_, 2);
v_exprMap_5268_ = lean_ctor_get(v_snd_5260_, 3);
v_recursorRuleMap_5269_ = lean_ctor_get(v_snd_5260_, 4);
v_constMap_5270_ = lean_ctor_get(v_snd_5260_, 5);
v_constOrder_5271_ = lean_ctor_get(v_snd_5260_, 6);
v_isSharedCheck_5298_ = !lean_is_exclusive(v_snd_5260_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5273_ = v_snd_5260_;
v_isShared_5274_ = v_isSharedCheck_5298_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_constOrder_5271_);
lean_inc(v_constMap_5270_);
lean_inc(v_recursorRuleMap_5269_);
lean_inc(v_exprMap_5268_);
lean_inc(v_levelMap_5267_);
lean_inc(v_nameMap_5266_);
lean_inc(v_stream_5265_);
lean_dec(v_snd_5260_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5298_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
uint8_t v___x_5275_; 
v___x_5275_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5267_, v_a_5138_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5279_; 
lean_del_object(v___x_5126_);
v___x_5276_ = lean_box(0);
v___x_5277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5267_, v_a_5138_, v_fst_5261_);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 2, v___x_5277_);
v___x_5279_ = v___x_5273_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_stream_5265_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_nameMap_5266_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v___x_5277_);
lean_ctor_set(v_reuseFailAlloc_5286_, 3, v_exprMap_5268_);
lean_ctor_set(v_reuseFailAlloc_5286_, 4, v_recursorRuleMap_5269_);
lean_ctor_set(v_reuseFailAlloc_5286_, 5, v_constMap_5270_);
lean_ctor_set(v_reuseFailAlloc_5286_, 6, v_constOrder_5271_);
v___x_5279_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
lean_object* v___x_5281_; 
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 1, v___x_5279_);
lean_ctor_set(v___x_5263_, 0, v___x_5276_);
v___x_5281_ = v___x_5263_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v___x_5279_);
v___x_5281_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
lean_object* v___x_5283_; 
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 0, v___x_5281_);
v___x_5283_ = v___x_5258_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
}
else
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5293_; 
lean_del_object(v___x_5273_);
lean_dec_ref(v_constOrder_5271_);
lean_dec_ref(v_constMap_5270_);
lean_dec_ref(v_recursorRuleMap_5269_);
lean_dec_ref(v_exprMap_5268_);
lean_dec_ref(v_levelMap_5267_);
lean_dec_ref(v_nameMap_5266_);
lean_dec_ref(v_stream_5265_);
lean_del_object(v___x_5263_);
lean_dec(v_fst_5261_);
v___x_5287_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5288_ = l_Nat_reprFast(v_a_5138_);
v___x_5289_ = lean_string_append(v___x_5287_, v___x_5288_);
lean_dec_ref(v___x_5288_);
v___x_5290_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5291_ = lean_string_append(v___x_5289_, v___x_5290_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 18);
lean_ctor_set(v___x_5126_, 0, v___x_5291_);
v___x_5293_ = v___x_5126_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5291_);
v___x_5293_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
lean_object* v___x_5295_; 
if (v_isShared_5259_ == 0)
{
lean_ctor_set_tag(v___x_5258_, 1);
lean_ctor_set(v___x_5258_, 0, v___x_5293_);
v___x_5295_ = v___x_5258_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v___x_5293_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_dec(v_a_5138_);
lean_del_object(v___x_5126_);
v_a_5301_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5255_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5255_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
else
{
lean_dec(v_a_5138_);
lean_dec(v_snd_5137_);
lean_dec(v_tail_5135_);
lean_del_object(v___x_5126_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_5136_);
if (lean_obj_tag(v_tail_5135_) == 0)
{
lean_object* v___x_5309_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5309_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_snd_5137_, v_a_4424_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5354_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5312_ = v___x_5309_;
v_isShared_5313_ = v_isSharedCheck_5354_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5309_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5354_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v_snd_5314_; lean_object* v_fst_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5353_; 
v_snd_5314_ = lean_ctor_get(v_a_5310_, 1);
v_fst_5315_ = lean_ctor_get(v_a_5310_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_a_5310_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5317_ = v_a_5310_;
v_isShared_5318_ = v_isSharedCheck_5353_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_snd_5314_);
lean_inc(v_fst_5315_);
lean_dec(v_a_5310_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5353_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v_stream_5319_; lean_object* v_nameMap_5320_; lean_object* v_levelMap_5321_; lean_object* v_exprMap_5322_; lean_object* v_recursorRuleMap_5323_; lean_object* v_constMap_5324_; lean_object* v_constOrder_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5352_; 
v_stream_5319_ = lean_ctor_get(v_snd_5314_, 0);
v_nameMap_5320_ = lean_ctor_get(v_snd_5314_, 1);
v_levelMap_5321_ = lean_ctor_get(v_snd_5314_, 2);
v_exprMap_5322_ = lean_ctor_get(v_snd_5314_, 3);
v_recursorRuleMap_5323_ = lean_ctor_get(v_snd_5314_, 4);
v_constMap_5324_ = lean_ctor_get(v_snd_5314_, 5);
v_constOrder_5325_ = lean_ctor_get(v_snd_5314_, 6);
v_isSharedCheck_5352_ = !lean_is_exclusive(v_snd_5314_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5327_ = v_snd_5314_;
v_isShared_5328_ = v_isSharedCheck_5352_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_constOrder_5325_);
lean_inc(v_constMap_5324_);
lean_inc(v_recursorRuleMap_5323_);
lean_inc(v_exprMap_5322_);
lean_inc(v_levelMap_5321_);
lean_inc(v_nameMap_5320_);
lean_inc(v_stream_5319_);
lean_dec(v_snd_5314_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5352_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
uint8_t v___x_5329_; 
v___x_5329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5321_, v_a_5138_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; 
lean_del_object(v___x_5126_);
v___x_5330_ = lean_box(0);
v___x_5331_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5321_, v_a_5138_, v_fst_5315_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 2, v___x_5331_);
v___x_5333_ = v___x_5327_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_stream_5319_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v_nameMap_5320_);
lean_ctor_set(v_reuseFailAlloc_5340_, 2, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5340_, 3, v_exprMap_5322_);
lean_ctor_set(v_reuseFailAlloc_5340_, 4, v_recursorRuleMap_5323_);
lean_ctor_set(v_reuseFailAlloc_5340_, 5, v_constMap_5324_);
lean_ctor_set(v_reuseFailAlloc_5340_, 6, v_constOrder_5325_);
v___x_5333_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5335_; 
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 1, v___x_5333_);
lean_ctor_set(v___x_5317_, 0, v___x_5330_);
v___x_5335_ = v___x_5317_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5337_; 
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5335_);
v___x_5337_ = v___x_5312_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
}
else
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5347_; 
lean_del_object(v___x_5327_);
lean_dec_ref(v_constOrder_5325_);
lean_dec_ref(v_constMap_5324_);
lean_dec_ref(v_recursorRuleMap_5323_);
lean_dec_ref(v_exprMap_5322_);
lean_dec_ref(v_levelMap_5321_);
lean_dec_ref(v_nameMap_5320_);
lean_dec_ref(v_stream_5319_);
lean_del_object(v___x_5317_);
lean_dec(v_fst_5315_);
v___x_5341_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5342_ = l_Nat_reprFast(v_a_5138_);
v___x_5343_ = lean_string_append(v___x_5341_, v___x_5342_);
lean_dec_ref(v___x_5342_);
v___x_5344_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5345_ = lean_string_append(v___x_5343_, v___x_5344_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 18);
lean_ctor_set(v___x_5126_, 0, v___x_5345_);
v___x_5347_ = v___x_5126_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
lean_object* v___x_5349_; 
if (v_isShared_5313_ == 0)
{
lean_ctor_set_tag(v___x_5312_, 1);
lean_ctor_set(v___x_5312_, 0, v___x_5347_);
v___x_5349_ = v___x_5312_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
lean_dec(v_a_5138_);
lean_del_object(v___x_5126_);
v_a_5355_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5309_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5309_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
else
{
lean_dec(v_a_5138_);
lean_dec(v_snd_5137_);
lean_dec(v_tail_5135_);
lean_del_object(v___x_5126_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_mantissa_5128_);
lean_del_object(v___x_5126_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_exponent_5129_);
lean_dec(v_mantissa_5128_);
lean_del_object(v___x_5126_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec_ref(v_fst_4459_);
if (lean_obj_tag(v_snd_4460_) == 2)
{
lean_object* v_n_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5491_; 
v_n_5364_ = lean_ctor_get(v_snd_4460_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_snd_4460_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5366_ = v_snd_4460_;
v_isShared_5367_ = v_isSharedCheck_5491_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_n_5364_);
lean_dec(v_snd_4460_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5491_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v_mantissa_5368_; lean_object* v_exponent_5369_; lean_object* v_natZero_5370_; lean_object* v_intZero_5371_; uint8_t v_isNeg_5372_; 
v_mantissa_5368_ = lean_ctor_get(v_n_5364_, 0);
lean_inc(v_mantissa_5368_);
v_exponent_5369_ = lean_ctor_get(v_n_5364_, 1);
lean_inc(v_exponent_5369_);
lean_dec_ref(v_n_5364_);
v_natZero_5370_ = lean_unsigned_to_nat(0u);
v_intZero_5371_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5372_ = lean_int_dec_lt(v_mantissa_5368_, v_intZero_5371_);
if (v_isNeg_5372_ == 0)
{
uint8_t v___x_5373_; 
v___x_5373_ = lean_nat_dec_eq(v_exponent_5369_, v_natZero_5370_);
lean_dec(v_exponent_5369_);
if (v___x_5373_ == 0)
{
lean_dec(v_mantissa_5368_);
lean_del_object(v___x_5366_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_4461_) == 1)
{
lean_object* v_head_5374_; lean_object* v_tail_5375_; lean_object* v_fst_5376_; lean_object* v_snd_5377_; lean_object* v_a_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_head_5374_ = lean_ctor_get(v_tail_4461_, 0);
lean_inc(v_head_5374_);
v_tail_5375_ = lean_ctor_get(v_tail_4461_, 1);
lean_inc(v_tail_5375_);
lean_dec_ref_known(v_tail_4461_, 2);
v_fst_5376_ = lean_ctor_get(v_head_5374_, 0);
lean_inc(v_fst_5376_);
v_snd_5377_ = lean_ctor_get(v_head_5374_, 1);
lean_inc(v_snd_5377_);
lean_dec(v_head_5374_);
v_a_5378_ = lean_nat_abs(v_mantissa_5368_);
lean_dec(v_mantissa_5368_);
v___x_5379_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_5380_ = lean_string_dec_eq(v_fst_5376_, v___x_5379_);
if (v___x_5380_ == 0)
{
lean_object* v___x_5381_; uint8_t v___x_5382_; 
v___x_5381_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24));
v___x_5382_ = lean_string_dec_eq(v_fst_5376_, v___x_5381_);
lean_dec(v_fst_5376_);
if (v___x_5382_ == 0)
{
lean_dec(v_a_5378_);
lean_dec(v_snd_5377_);
lean_dec(v_tail_5375_);
lean_del_object(v___x_5366_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
else
{
if (lean_obj_tag(v_tail_5375_) == 0)
{
lean_object* v___x_5383_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5383_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_snd_5377_, v_a_4424_);
lean_dec(v_snd_5377_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v_a_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5428_; 
v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5386_ = v___x_5383_;
v_isShared_5387_ = v_isSharedCheck_5428_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_a_5384_);
lean_dec(v___x_5383_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5428_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v_snd_5388_; lean_object* v_fst_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5427_; 
v_snd_5388_ = lean_ctor_get(v_a_5384_, 1);
v_fst_5389_ = lean_ctor_get(v_a_5384_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v_a_5384_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5391_ = v_a_5384_;
v_isShared_5392_ = v_isSharedCheck_5427_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_snd_5388_);
lean_inc(v_fst_5389_);
lean_dec(v_a_5384_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5427_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v_stream_5393_; lean_object* v_nameMap_5394_; lean_object* v_levelMap_5395_; lean_object* v_exprMap_5396_; lean_object* v_recursorRuleMap_5397_; lean_object* v_constMap_5398_; lean_object* v_constOrder_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5426_; 
v_stream_5393_ = lean_ctor_get(v_snd_5388_, 0);
v_nameMap_5394_ = lean_ctor_get(v_snd_5388_, 1);
v_levelMap_5395_ = lean_ctor_get(v_snd_5388_, 2);
v_exprMap_5396_ = lean_ctor_get(v_snd_5388_, 3);
v_recursorRuleMap_5397_ = lean_ctor_get(v_snd_5388_, 4);
v_constMap_5398_ = lean_ctor_get(v_snd_5388_, 5);
v_constOrder_5399_ = lean_ctor_get(v_snd_5388_, 6);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_snd_5388_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5401_ = v_snd_5388_;
v_isShared_5402_ = v_isSharedCheck_5426_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_constOrder_5399_);
lean_inc(v_constMap_5398_);
lean_inc(v_recursorRuleMap_5397_);
lean_inc(v_exprMap_5396_);
lean_inc(v_levelMap_5395_);
lean_inc(v_nameMap_5394_);
lean_inc(v_stream_5393_);
lean_dec(v_snd_5388_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5426_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
uint8_t v___x_5403_; 
v___x_5403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_nameMap_5394_, v_a_5378_);
if (v___x_5403_ == 0)
{
lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5407_; 
lean_del_object(v___x_5366_);
v___x_5404_ = lean_box(0);
v___x_5405_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5394_, v_a_5378_, v_fst_5389_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 1, v___x_5405_);
v___x_5407_ = v___x_5401_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_stream_5393_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v___x_5405_);
lean_ctor_set(v_reuseFailAlloc_5414_, 2, v_levelMap_5395_);
lean_ctor_set(v_reuseFailAlloc_5414_, 3, v_exprMap_5396_);
lean_ctor_set(v_reuseFailAlloc_5414_, 4, v_recursorRuleMap_5397_);
lean_ctor_set(v_reuseFailAlloc_5414_, 5, v_constMap_5398_);
lean_ctor_set(v_reuseFailAlloc_5414_, 6, v_constOrder_5399_);
v___x_5407_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5407_);
lean_ctor_set(v___x_5391_, 0, v___x_5404_);
v___x_5409_ = v___x_5391_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5404_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v___x_5407_);
v___x_5409_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5411_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 0, v___x_5409_);
v___x_5411_ = v___x_5386_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
else
{
lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
lean_del_object(v___x_5401_);
lean_dec_ref(v_constOrder_5399_);
lean_dec_ref(v_constMap_5398_);
lean_dec_ref(v_recursorRuleMap_5397_);
lean_dec_ref(v_exprMap_5396_);
lean_dec_ref(v_levelMap_5395_);
lean_dec_ref(v_nameMap_5394_);
lean_dec_ref(v_stream_5393_);
lean_del_object(v___x_5391_);
lean_dec(v_fst_5389_);
v___x_5415_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_5416_ = l_Nat_reprFast(v_a_5378_);
v___x_5417_ = lean_string_append(v___x_5415_, v___x_5416_);
lean_dec_ref(v___x_5416_);
v___x_5418_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5419_ = lean_string_append(v___x_5417_, v___x_5418_);
if (v_isShared_5367_ == 0)
{
lean_ctor_set_tag(v___x_5366_, 18);
lean_ctor_set(v___x_5366_, 0, v___x_5419_);
v___x_5421_ = v___x_5366_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set_tag(v___x_5386_, 1);
lean_ctor_set(v___x_5386_, 0, v___x_5421_);
v___x_5423_ = v___x_5386_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec(v_a_5378_);
lean_del_object(v___x_5366_);
v_a_5429_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5383_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5383_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_dec(v_a_5378_);
lean_dec(v_snd_5377_);
lean_dec(v_tail_5375_);
lean_del_object(v___x_5366_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_fst_5376_);
if (lean_obj_tag(v_tail_5375_) == 0)
{
lean_object* v___x_5437_; 
lean_del_object(v___x_4444_);
lean_dec(v_kvPairs_4442_);
lean_del_object(v___x_4440_);
v___x_5437_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_snd_5377_, v_a_4424_);
lean_dec(v_snd_5377_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5482_; 
v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5437_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5440_ = v___x_5437_;
v_isShared_5441_ = v_isSharedCheck_5482_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5437_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5482_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v_snd_5442_; lean_object* v_fst_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5481_; 
v_snd_5442_ = lean_ctor_get(v_a_5438_, 1);
v_fst_5443_ = lean_ctor_get(v_a_5438_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v_a_5438_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5445_ = v_a_5438_;
v_isShared_5446_ = v_isSharedCheck_5481_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_snd_5442_);
lean_inc(v_fst_5443_);
lean_dec(v_a_5438_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5481_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v_stream_5447_; lean_object* v_nameMap_5448_; lean_object* v_levelMap_5449_; lean_object* v_exprMap_5450_; lean_object* v_recursorRuleMap_5451_; lean_object* v_constMap_5452_; lean_object* v_constOrder_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5480_; 
v_stream_5447_ = lean_ctor_get(v_snd_5442_, 0);
v_nameMap_5448_ = lean_ctor_get(v_snd_5442_, 1);
v_levelMap_5449_ = lean_ctor_get(v_snd_5442_, 2);
v_exprMap_5450_ = lean_ctor_get(v_snd_5442_, 3);
v_recursorRuleMap_5451_ = lean_ctor_get(v_snd_5442_, 4);
v_constMap_5452_ = lean_ctor_get(v_snd_5442_, 5);
v_constOrder_5453_ = lean_ctor_get(v_snd_5442_, 6);
v_isSharedCheck_5480_ = !lean_is_exclusive(v_snd_5442_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5455_ = v_snd_5442_;
v_isShared_5456_ = v_isSharedCheck_5480_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_constOrder_5453_);
lean_inc(v_constMap_5452_);
lean_inc(v_recursorRuleMap_5451_);
lean_inc(v_exprMap_5450_);
lean_inc(v_levelMap_5449_);
lean_inc(v_nameMap_5448_);
lean_inc(v_stream_5447_);
lean_dec(v_snd_5442_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5480_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
uint8_t v___x_5457_; 
v___x_5457_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_nameMap_5448_, v_a_5378_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5461_; 
lean_del_object(v___x_5366_);
v___x_5458_ = lean_box(0);
v___x_5459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5448_, v_a_5378_, v_fst_5443_);
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 1, v___x_5459_);
v___x_5461_ = v___x_5455_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_stream_5447_);
lean_ctor_set(v_reuseFailAlloc_5468_, 1, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5468_, 2, v_levelMap_5449_);
lean_ctor_set(v_reuseFailAlloc_5468_, 3, v_exprMap_5450_);
lean_ctor_set(v_reuseFailAlloc_5468_, 4, v_recursorRuleMap_5451_);
lean_ctor_set(v_reuseFailAlloc_5468_, 5, v_constMap_5452_);
lean_ctor_set(v_reuseFailAlloc_5468_, 6, v_constOrder_5453_);
v___x_5461_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
lean_object* v___x_5463_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5461_);
lean_ctor_set(v___x_5445_, 0, v___x_5458_);
v___x_5463_ = v___x_5445_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5458_);
lean_ctor_set(v_reuseFailAlloc_5467_, 1, v___x_5461_);
v___x_5463_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
lean_object* v___x_5465_; 
if (v_isShared_5441_ == 0)
{
lean_ctor_set(v___x_5440_, 0, v___x_5463_);
v___x_5465_ = v___x_5440_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
else
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5475_; 
lean_del_object(v___x_5455_);
lean_dec_ref(v_constOrder_5453_);
lean_dec_ref(v_constMap_5452_);
lean_dec_ref(v_recursorRuleMap_5451_);
lean_dec_ref(v_exprMap_5450_);
lean_dec_ref(v_levelMap_5449_);
lean_dec_ref(v_nameMap_5448_);
lean_dec_ref(v_stream_5447_);
lean_del_object(v___x_5445_);
lean_dec(v_fst_5443_);
v___x_5469_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_5470_ = l_Nat_reprFast(v_a_5378_);
v___x_5471_ = lean_string_append(v___x_5469_, v___x_5470_);
lean_dec_ref(v___x_5470_);
v___x_5472_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5473_ = lean_string_append(v___x_5471_, v___x_5472_);
if (v_isShared_5367_ == 0)
{
lean_ctor_set_tag(v___x_5366_, 18);
lean_ctor_set(v___x_5366_, 0, v___x_5473_);
v___x_5475_ = v___x_5366_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5473_);
v___x_5475_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
lean_object* v___x_5477_; 
if (v_isShared_5441_ == 0)
{
lean_ctor_set_tag(v___x_5440_, 1);
lean_ctor_set(v___x_5440_, 0, v___x_5475_);
v___x_5477_ = v___x_5440_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_a_5378_);
lean_del_object(v___x_5366_);
v_a_5483_ = lean_ctor_get(v___x_5437_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5437_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5437_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5437_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
else
{
lean_dec(v_a_5378_);
lean_dec(v_snd_5377_);
lean_dec(v_tail_5375_);
lean_del_object(v___x_5366_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_mantissa_5368_);
lean_del_object(v___x_5366_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_exponent_5369_);
lean_dec(v_mantissa_5368_);
lean_del_object(v___x_5366_);
lean_dec(v_tail_4461_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v_snd_4460_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
v___jp_5492_:
{
if (lean_obj_tag(v___y_5493_) == 1)
{
lean_object* v_head_5494_; lean_object* v_tail_5495_; lean_object* v_fst_5496_; lean_object* v_snd_5497_; 
v_head_5494_ = lean_ctor_get(v___y_5493_, 0);
lean_inc(v_head_5494_);
v_tail_5495_ = lean_ctor_get(v___y_5493_, 1);
lean_inc(v_tail_5495_);
lean_dec_ref_known(v___y_5493_, 2);
v_fst_5496_ = lean_ctor_get(v_head_5494_, 0);
lean_inc(v_fst_5496_);
v_snd_5497_ = lean_ctor_get(v_head_5494_, 1);
lean_inc(v_snd_5497_);
lean_dec(v_head_5494_);
v_fst_4459_ = v_fst_5496_;
v_snd_4460_ = v_snd_5497_;
v_tail_4461_ = v_tail_5495_;
goto v___jp_4458_;
}
else
{
lean_dec(v___y_5493_);
lean_dec_ref(v_a_4424_);
goto v___jp_4446_;
}
}
}
}
else
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4424_);
v___x_5527_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_5527_);
v___x_5529_ = v___x_4440_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___boxed(lean_object* v_line_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_line_5532_, v_a_5533_);
return v_res_5535_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object* v_00_u03b2_5536_, lean_object* v_m_5537_, lean_object* v_a_5538_){
_start:
{
uint8_t v___x_5539_; 
v___x_5539_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_m_5537_, v_a_5538_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object* v_00_u03b2_5540_, lean_object* v_m_5541_, lean_object* v_a_5542_){
_start:
{
uint8_t v_res_5543_; lean_object* v_r_5544_; 
v_res_5543_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_00_u03b2_5540_, v_m_5541_, v_a_5542_);
lean_dec(v_a_5542_);
lean_dec_ref(v_m_5541_);
v_r_5544_ = lean_box(v_res_5543_);
return v_r_5544_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(lean_object* v_a_5545_){
_start:
{
lean_object* v_stream_5547_; lean_object* v_getLine_5548_; lean_object* v___x_5549_; 
v_stream_5547_ = lean_ctor_get(v_a_5545_, 0);
v_getLine_5548_ = lean_ctor_get(v_stream_5547_, 3);
lean_inc_ref(v_getLine_5548_);
v___x_5549_ = lean_apply_1(v_getLine_5548_, lean_box(0));
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5566_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5552_ = v___x_5549_;
v_isShared_5553_ = v_isSharedCheck_5566_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5549_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5566_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; uint8_t v___x_5556_; 
v___x_5554_ = lean_string_utf8_byte_size(v_a_5550_);
v___x_5555_ = lean_unsigned_to_nat(0u);
v___x_5556_ = lean_nat_dec_eq(v___x_5554_, v___x_5555_);
if (v___x_5556_ == 0)
{
lean_object* v___x_5557_; 
lean_del_object(v___x_5552_);
v___x_5557_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_a_5550_, v_a_5545_);
if (lean_obj_tag(v___x_5557_) == 0)
{
lean_object* v_a_5558_; lean_object* v_snd_5559_; 
v_a_5558_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_a_5558_);
lean_dec_ref_known(v___x_5557_, 1);
v_snd_5559_ = lean_ctor_get(v_a_5558_, 1);
lean_inc(v_snd_5559_);
lean_dec(v_a_5558_);
v_a_5545_ = v_snd_5559_;
goto _start;
}
else
{
return v___x_5557_;
}
}
else
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5564_; 
lean_dec(v_a_5550_);
v___x_5561_ = lean_box(0);
v___x_5562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5562_, 0, v___x_5561_);
lean_ctor_set(v___x_5562_, 1, v_a_5545_);
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 0, v___x_5562_);
v___x_5564_ = v___x_5552_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5562_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec_ref(v_a_5545_);
v_a_5567_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5549_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5549_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go___boxed(lean_object* v_a_5575_, lean_object* v_a_5576_){
_start:
{
lean_object* v_res_5577_; 
v_res_5577_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5575_);
return v_res_5577_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(lean_object* v_a_5578_){
_start:
{
lean_object* v___x_5580_; 
v___x_5580_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5578_);
return v___x_5580_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems___boxed(lean_object* v_a_5581_, lean_object* v_a_5582_){
_start:
{
lean_object* v_res_5583_; 
v_res_5583_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(v_a_5581_);
return v_res_5583_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(lean_object* v_a_5584_){
_start:
{
lean_object* v_stream_5586_; lean_object* v_getLine_5587_; lean_object* v___x_5588_; 
v_stream_5586_ = lean_ctor_get(v_a_5584_, 0);
v_getLine_5587_ = lean_ctor_get(v_stream_5586_, 3);
lean_inc_ref(v_getLine_5587_);
v___x_5588_ = lean_apply_1(v_getLine_5587_, lean_box(0));
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5597_; 
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; 
v_unused_5598_ = lean_ctor_get(v___x_5588_, 0);
lean_dec(v_unused_5598_);
v___x_5590_ = v___x_5588_;
v_isShared_5591_ = v_isSharedCheck_5597_;
goto v_resetjp_5589_;
}
else
{
lean_dec(v___x_5588_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5597_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5592_ = lean_box(0);
v___x_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5593_, 0, v___x_5592_);
lean_ctor_set(v___x_5593_, 1, v_a_5584_);
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 0, v___x_5593_);
v___x_5595_ = v___x_5590_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
lean_dec_ref(v_a_5584_);
v_a_5599_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5588_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5588_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata___boxed(lean_object* v_a_5607_, lean_object* v_a_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5607_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(lean_object* v_a_5610_){
_start:
{
lean_object* v___x_5612_; 
v___x_5612_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5610_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_a_5613_; lean_object* v_snd_5614_; lean_object* v___x_5615_; 
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_a_5613_);
lean_dec_ref_known(v___x_5612_, 1);
v_snd_5614_ = lean_ctor_get(v_a_5613_, 1);
lean_inc(v_snd_5614_);
lean_dec(v_a_5613_);
v___x_5615_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_snd_5614_);
return v___x_5615_;
}
else
{
return v___x_5612_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed(lean_object* v_a_5616_, lean_object* v_a_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(v_a_5616_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream(lean_object* v_stream_5619_){
_start:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; 
v___x_5621_ = lean_alloc_closure((void*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed), 2, 0);
v___x_5622_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v___x_5621_, v_stream_5619_);
if (lean_obj_tag(v___x_5622_) == 0)
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5641_; 
v_a_5623_ = lean_ctor_get(v___x_5622_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5622_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5625_ = v___x_5622_;
v_isShared_5626_ = v_isSharedCheck_5641_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5622_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5641_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v_snd_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5639_; 
v_snd_5627_ = lean_ctor_get(v_a_5623_, 1);
v_isSharedCheck_5639_ = !lean_is_exclusive(v_a_5623_);
if (v_isSharedCheck_5639_ == 0)
{
lean_object* v_unused_5640_; 
v_unused_5640_ = lean_ctor_get(v_a_5623_, 0);
lean_dec(v_unused_5640_);
v___x_5629_ = v_a_5623_;
v_isShared_5630_ = v_isSharedCheck_5639_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_snd_5627_);
lean_dec(v_a_5623_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5639_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v_constMap_5631_; lean_object* v_constOrder_5632_; lean_object* v___x_5634_; 
v_constMap_5631_ = lean_ctor_get(v_snd_5627_, 5);
lean_inc_ref(v_constMap_5631_);
v_constOrder_5632_ = lean_ctor_get(v_snd_5627_, 6);
lean_inc_ref(v_constOrder_5632_);
lean_dec(v_snd_5627_);
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 1, v_constOrder_5632_);
lean_ctor_set(v___x_5629_, 0, v_constMap_5631_);
v___x_5634_ = v___x_5629_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_constMap_5631_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_constOrder_5632_);
v___x_5634_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5636_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 0, v___x_5634_);
v___x_5636_ = v___x_5625_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v___x_5634_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
return v___x_5636_;
}
}
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_a_5642_ = lean_ctor_get(v___x_5622_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5622_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5622_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5622_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream___boxed(lean_object* v_stream_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l_LeanExport_parseStream(v_stream_5650_);
return v_res_5652_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_String(uint8_t builtin);
lean_object* runtime_initialize_LeanExport_Json(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanExport_Parse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LeanExport_instInhabitedExportedEnv_default = _init_l_LeanExport_instInhabitedExportedEnv_default();
lean_mark_persistent(l_LeanExport_instInhabitedExportedEnv_default);
l_LeanExport_instInhabitedExportedEnv = _init_l_LeanExport_instInhabitedExportedEnv();
lean_mark_persistent(l_LeanExport_instInhabitedExportedEnv);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanExport_Parse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_String(uint8_t builtin);
lean_object* initialize_LeanExport_Json(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport_Parse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanExport_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanExport_Parse(builtin);
}
#ifdef __cplusplus
}
#endif

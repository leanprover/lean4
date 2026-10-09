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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(lean_object* v_a_81_, lean_object* v_x_82_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_81_ = stack[0].m_obj;
lean_object* v_x_82_ = stack[1].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_81_, v_x_82_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_89_, lean_object* v_x_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_89_, v_x_90_);
lean_dec(v_x_90_);
lean_dec(v_a_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(lean_object* v_m_93_, lean_object* v_a_94_, lean_object* v_b_95_){
_start:
{
lean_object* v_size_96_; lean_object* v_buckets_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_140_; 
v_size_96_ = lean_ctor_get(v_m_93_, 0);
v_buckets_97_ = lean_ctor_get(v_m_93_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_m_93_);
if (v_isSharedCheck_140_ == 0)
{
v___x_99_ = v_m_93_;
v_isShared_100_ = v_isSharedCheck_140_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_buckets_97_);
lean_inc(v_size_96_);
lean_dec(v_m_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_140_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v_fold_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v_bkt_114_; uint8_t v___x_115_; 
v___x_101_ = lean_array_get_size(v_buckets_97_);
v___x_102_ = lean_uint64_of_nat(v_a_94_);
v___x_103_ = 32ULL;
v___x_104_ = lean_uint64_shift_right(v___x_102_, v___x_103_);
v_fold_105_ = lean_uint64_xor(v___x_102_, v___x_104_);
v___x_106_ = 16ULL;
v___x_107_ = lean_uint64_shift_right(v_fold_105_, v___x_106_);
v___x_108_ = lean_uint64_xor(v_fold_105_, v___x_107_);
v___x_109_ = lean_uint64_to_usize(v___x_108_);
v___x_110_ = lean_usize_of_nat(v___x_101_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_sub(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_land(v___x_109_, v___x_112_);
v_bkt_114_ = lean_array_uget_borrowed(v_buckets_97_, v___x_113_);
v___x_115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_94_, v_bkt_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v_size_x27_117_; lean_object* v___x_118_; lean_object* v_buckets_x27_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v_size_x27_117_ = lean_nat_add(v_size_96_, v___x_116_);
lean_dec(v_size_96_);
lean_inc(v_bkt_114_);
v___x_118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_118_, 0, v_a_94_);
lean_ctor_set(v___x_118_, 1, v_b_95_);
lean_ctor_set(v___x_118_, 2, v_bkt_114_);
v_buckets_x27_119_ = lean_array_uset(v_buckets_97_, v___x_113_, v___x_118_);
v___x_120_ = lean_unsigned_to_nat(4u);
v___x_121_ = lean_nat_mul(v_size_x27_117_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(3u);
v___x_123_ = lean_nat_div(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_array_get_size(v_buckets_x27_119_);
v___x_125_ = lean_nat_dec_le(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
if (v___x_125_ == 0)
{
lean_object* v_val_126_; lean_object* v___x_128_; 
v_val_126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_buckets_x27_119_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_val_126_);
lean_ctor_set(v___x_99_, 0, v_size_x27_117_);
v___x_128_ = v___x_99_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_x27_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_val_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_131_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_buckets_x27_119_);
lean_ctor_set(v___x_99_, 0, v_size_x27_117_);
v___x_131_ = v___x_99_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_117_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_buckets_x27_119_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v___x_133_; lean_object* v_buckets_x27_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
lean_inc(v_bkt_114_);
v___x_133_ = lean_box(0);
v_buckets_x27_134_ = lean_array_uset(v_buckets_97_, v___x_113_, v___x_133_);
v___x_135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_94_, v_b_95_, v_bkt_114_);
v___x_136_ = lean_array_uset(v_buckets_x27_134_, v___x_113_, v___x_135_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___x_136_);
v___x_138_ = v___x_99_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_96_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = lean_unsigned_to_nat(16u);
v___x_143_ = lean_mk_array(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_149_, v___x_148_, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_153_, v___x_152_, v___x_151_);
return v___x_154_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(lean_object* v_x_157_, lean_object* v_stream_158_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_161_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2);
v___x_162_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3);
v___x_163_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4));
v___x_164_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_164_, 0, v_stream_158_);
lean_ctor_set(v___x_164_, 1, v___x_161_);
lean_ctor_set(v___x_164_, 2, v___x_162_);
lean_ctor_set(v___x_164_, 3, v___x_160_);
lean_ctor_set(v___x_164_, 4, v___x_160_);
lean_ctor_set(v___x_164_, 5, v___x_160_);
lean_ctor_set(v___x_164_, 6, v___x_163_);
v___x_165_ = lean_apply_2(v_x_157_, v___x_164_, lean_box(0));
return v___x_165_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_157_ = stack[0].m_obj;
lean_object* v_stream_158_ = stack[1].m_obj;
lean_object* v_res_166_;
v_res_166_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_157_, v_stream_158_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___boxed(lean_object* v_x_167_, lean_object* v_stream_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_167_, v_stream_168_);
return v_res_170_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(lean_object* v_00_u03b1_171_, lean_object* v_x_172_, lean_object* v_stream_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_172_, v_stream_173_);
return v___x_175_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_M_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_172_ = stack[1].m_obj;
lean_object* v_stream_173_ = stack[2].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(lean_box(0), v_x_172_, v_stream_173_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___boxed(lean_object* v_00_u03b1_177_, lean_object* v_x_178_, lean_object* v_stream_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(v_00_u03b1_177_, v_x_178_, v_stream_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0(lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_m_183_, v_a_184_, v_b_185_);
return v___x_186_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_188_ = stack[1].m_obj;
lean_object* v_x_189_ = stack[2].m_obj;
uint8_t v_res_191_;
v_res_191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(lean_box(0), v_a_188_, v_x_189_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(v_00_u03b2_192_, v_a_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec(v_a_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1(lean_object* v_00_u03b2_197_, lean_object* v_data_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_data_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2(lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_b_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_201_, v_b_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_205_, lean_object* v_i_206_, lean_object* v_source_207_, lean_object* v_target_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(v_i_206_, v_source_207_, v_target_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(v_x_211_, v_x_212_);
return v___x_213_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(lean_object* v_msg_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_216_, 0, v_msg_214_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_214_ = stack[0].m_obj;
lean_object* v_res_218_;
v_res_218_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(v_msg_214_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg___boxed(lean_object* v_msg_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(v_msg_219_);
return v_res_221_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail(lean_object* v_00_u03b1_222_, lean_object* v_msg_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_226_, 0, v_msg_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_fail_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_223_ = stack[1].m_obj;
lean_object* v_a_224_ = stack[2].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail(lean_box(0), v_msg_223_, v_a_224_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___boxed(lean_object* v_00_u03b1_229_, lean_object* v_msg_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail(v_00_u03b1_229_, v_msg_230_, v_a_231_);
lean_dec_ref(v_a_231_);
return v_res_233_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___f_236_; 
v___x_235_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_236_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_236_, 0, v___x_235_);
return v___f_236_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName(lean_object* v_nidx_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_nameMap_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; 
v_nameMap_241_ = lean_ctor_get(v_a_239_, 1);
v___f_242_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_243_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_nidx_238_);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_243_, v___f_242_, v_nameMap_241_, v_nidx_238_);
if (lean_obj_tag(v___x_244_) == 1)
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_nidx_238_);
v_val_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_val_245_);
lean_ctor_set(v___x_249_, 1, v_a_239_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 0);
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_244_);
lean_dec_ref(v_a_239_);
v___x_254_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_255_ = l_Nat_reprFast(v_nidx_238_);
v___x_256_ = lean_string_append(v___x_254_, v___x_255_);
lean_dec_ref(v___x_255_);
v___x_257_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_getName_0interp(lean_interpreter_value* stack)
{
lean_object* v_nidx_238_ = stack[0].m_obj;
lean_object* v_a_239_ = stack[1].m_obj;
lean_object* v_res_259_;
v_res_259_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getName(v_nidx_238_, v_a_239_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___boxed(lean_object* v_nidx_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getName(v_nidx_260_, v_a_261_);
return v_res_263_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object* v_nidx_266_, lean_object* v_n_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_stream_270_; lean_object* v_nameMap_271_; lean_object* v_levelMap_272_; lean_object* v_exprMap_273_; lean_object* v_recursorRuleMap_274_; lean_object* v_constMap_275_; lean_object* v_constOrder_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_297_; 
v_stream_270_ = lean_ctor_get(v_a_268_, 0);
v_nameMap_271_ = lean_ctor_get(v_a_268_, 1);
v_levelMap_272_ = lean_ctor_get(v_a_268_, 2);
v_exprMap_273_ = lean_ctor_get(v_a_268_, 3);
v_recursorRuleMap_274_ = lean_ctor_get(v_a_268_, 4);
v_constMap_275_ = lean_ctor_get(v_a_268_, 5);
v_constOrder_276_ = lean_ctor_get(v_a_268_, 6);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_268_);
if (v_isSharedCheck_297_ == 0)
{
v___x_278_ = v_a_268_;
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_constOrder_276_);
lean_inc(v_constMap_275_);
lean_inc(v_recursorRuleMap_274_);
lean_inc(v_exprMap_273_);
lean_inc(v_levelMap_272_);
lean_inc(v_nameMap_271_);
lean_inc(v_stream_270_);
lean_dec(v_a_268_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___f_280_; lean_object* v___f_281_; uint8_t v___x_282_; 
v___f_280_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_281_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_nidx_266_);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_281_, v___f_280_, v_nameMap_271_, v_nidx_266_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_box(0);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_281_, v___f_280_, v_nameMap_271_, v_nidx_266_, v_n_267_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_284_);
v___x_286_ = v___x_278_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_stream_270_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_levelMap_272_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_exprMap_273_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_recursorRuleMap_274_);
lean_ctor_set(v_reuseFailAlloc_289_, 5, v_constMap_275_);
lean_ctor_set(v_reuseFailAlloc_289_, 6, v_constOrder_276_);
v___x_286_ = v_reuseFailAlloc_289_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_283_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_del_object(v___x_278_);
lean_dec_ref(v_constOrder_276_);
lean_dec_ref(v_constMap_275_);
lean_dec_ref(v_recursorRuleMap_274_);
lean_dec_ref(v_exprMap_273_);
lean_dec_ref(v_levelMap_272_);
lean_dec_ref(v_nameMap_271_);
lean_dec_ref(v_stream_270_);
lean_dec(v_n_267_);
v___x_290_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_291_ = l_Nat_reprFast(v_nidx_266_);
v___x_292_ = lean_string_append(v___x_290_, v___x_291_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_addName_0interp(lean_interpreter_value* stack)
{
lean_object* v_nidx_266_ = stack[0].m_obj;
lean_object* v_n_267_ = stack[1].m_obj;
lean_object* v_a_268_ = stack[2].m_obj;
lean_object* v_res_298_;
v_res_298_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addName(v_nidx_266_, v_n_267_, v_a_268_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object* v_nidx_299_, lean_object* v_n_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addName(v_nidx_299_, v_n_300_, v_a_301_);
return v_res_303_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object* v_uidx_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_levelMap_308_; lean_object* v___f_309_; lean_object* v___f_310_; lean_object* v___x_311_; 
v_levelMap_308_ = lean_ctor_get(v_a_306_, 2);
v___f_309_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_310_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_305_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_310_, v___f_309_, v_levelMap_308_, v_uidx_305_);
if (lean_obj_tag(v___x_311_) == 1)
{
lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_uidx_305_);
v_val_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_val_312_);
lean_ctor_set(v___x_316_, 1, v_a_306_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 0);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v___x_311_);
lean_dec_ref(v_a_306_);
v___x_321_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_322_ = l_Nat_reprFast(v_uidx_305_);
v___x_323_ = lean_string_append(v___x_321_, v___x_322_);
lean_dec_ref(v___x_322_);
v___x_324_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_uidx_305_ = stack[0].m_obj;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_res_326_;
v_res_326_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(v_uidx_305_, v_a_306_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object* v_uidx_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(v_uidx_327_, v_a_328_);
return v_res_330_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object* v_uidx_332_, lean_object* v_l_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_stream_336_; lean_object* v_nameMap_337_; lean_object* v_levelMap_338_; lean_object* v_exprMap_339_; lean_object* v_recursorRuleMap_340_; lean_object* v_constMap_341_; lean_object* v_constOrder_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_363_; 
v_stream_336_ = lean_ctor_get(v_a_334_, 0);
v_nameMap_337_ = lean_ctor_get(v_a_334_, 1);
v_levelMap_338_ = lean_ctor_get(v_a_334_, 2);
v_exprMap_339_ = lean_ctor_get(v_a_334_, 3);
v_recursorRuleMap_340_ = lean_ctor_get(v_a_334_, 4);
v_constMap_341_ = lean_ctor_get(v_a_334_, 5);
v_constOrder_342_ = lean_ctor_get(v_a_334_, 6);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_363_ == 0)
{
v___x_344_ = v_a_334_;
v_isShared_345_ = v_isSharedCheck_363_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_constOrder_342_);
lean_inc(v_constMap_341_);
lean_inc(v_recursorRuleMap_340_);
lean_inc(v_exprMap_339_);
lean_inc(v_levelMap_338_);
lean_inc(v_nameMap_337_);
lean_inc(v_stream_336_);
lean_dec(v_a_334_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_363_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___f_346_; lean_object* v___f_347_; uint8_t v___x_348_; 
v___f_346_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_347_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_332_);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_347_, v___f_346_, v_levelMap_338_, v_uidx_332_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = lean_box(0);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_347_, v___f_346_, v_levelMap_338_, v_uidx_332_, v_l_333_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 2, v___x_350_);
v___x_352_ = v___x_344_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_stream_336_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_nameMap_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_exprMap_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_recursorRuleMap_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_constMap_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_constOrder_342_);
v___x_352_ = v_reuseFailAlloc_355_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_del_object(v___x_344_);
lean_dec_ref(v_constOrder_342_);
lean_dec_ref(v_constMap_341_);
lean_dec_ref(v_recursorRuleMap_340_);
lean_dec_ref(v_exprMap_339_);
lean_dec_ref(v_levelMap_338_);
lean_dec_ref(v_nameMap_337_);
lean_dec_ref(v_stream_336_);
lean_dec(v_l_333_);
v___x_356_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_357_ = l_Nat_reprFast(v_uidx_332_);
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
v___x_361_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_uidx_332_ = stack[0].m_obj;
lean_object* v_l_333_ = stack[1].m_obj;
lean_object* v_a_334_ = stack[2].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(v_uidx_332_, v_l_333_, v_a_334_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object* v_uidx_365_, lean_object* v_l_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(v_uidx_365_, v_l_366_, v_a_367_);
return v_res_369_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object* v_eidx_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_exprMap_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___x_377_; 
v_exprMap_374_ = lean_ctor_get(v_a_372_, 3);
v___f_375_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_376_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_371_);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_376_, v___f_375_, v_exprMap_374_, v_eidx_371_);
if (lean_obj_tag(v___x_377_) == 1)
{
lean_object* v_val_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
lean_dec(v_eidx_371_);
v_val_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_val_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_val_378_);
lean_ctor_set(v___x_382_, 1, v_a_372_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v___x_377_);
lean_dec_ref(v_a_372_);
v___x_387_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_388_ = l_Nat_reprFast(v_eidx_371_);
v___x_389_ = lean_string_append(v___x_387_, v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_eidx_371_ = stack[0].m_obj;
lean_object* v_a_372_ = stack[1].m_obj;
lean_object* v_res_392_;
v_res_392_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(v_eidx_371_, v_a_372_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object* v_eidx_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(v_eidx_393_, v_a_394_);
return v_res_396_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object* v_eidx_398_, lean_object* v_e_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_stream_402_; lean_object* v_nameMap_403_; lean_object* v_levelMap_404_; lean_object* v_exprMap_405_; lean_object* v_recursorRuleMap_406_; lean_object* v_constMap_407_; lean_object* v_constOrder_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_429_; 
v_stream_402_ = lean_ctor_get(v_a_400_, 0);
v_nameMap_403_ = lean_ctor_get(v_a_400_, 1);
v_levelMap_404_ = lean_ctor_get(v_a_400_, 2);
v_exprMap_405_ = lean_ctor_get(v_a_400_, 3);
v_recursorRuleMap_406_ = lean_ctor_get(v_a_400_, 4);
v_constMap_407_ = lean_ctor_get(v_a_400_, 5);
v_constOrder_408_ = lean_ctor_get(v_a_400_, 6);
v_isSharedCheck_429_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_429_ == 0)
{
v___x_410_ = v_a_400_;
v_isShared_411_ = v_isSharedCheck_429_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_constOrder_408_);
lean_inc(v_constMap_407_);
lean_inc(v_recursorRuleMap_406_);
lean_inc(v_exprMap_405_);
lean_inc(v_levelMap_404_);
lean_inc(v_nameMap_403_);
lean_inc(v_stream_402_);
lean_dec(v_a_400_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_429_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___f_412_; lean_object* v___f_413_; uint8_t v___x_414_; 
v___f_412_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_413_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_398_);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_413_, v___f_412_, v_exprMap_405_, v_eidx_398_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_box(0);
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_413_, v___f_412_, v_exprMap_405_, v_eidx_398_, v_e_399_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 3, v___x_416_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_stream_402_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_nameMap_403_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_levelMap_404_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_recursorRuleMap_406_);
lean_ctor_set(v_reuseFailAlloc_421_, 5, v_constMap_407_);
lean_ctor_set(v_reuseFailAlloc_421_, 6, v_constOrder_408_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_415_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_410_);
lean_dec_ref(v_constOrder_408_);
lean_dec_ref(v_constMap_407_);
lean_dec_ref(v_recursorRuleMap_406_);
lean_dec_ref(v_exprMap_405_);
lean_dec_ref(v_levelMap_404_);
lean_dec_ref(v_nameMap_403_);
lean_dec_ref(v_stream_402_);
lean_dec_ref(v_e_399_);
v___x_422_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_423_ = l_Nat_reprFast(v_eidx_398_);
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
lean_dec_ref(v___x_423_);
v___x_425_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_426_ = lean_string_append(v___x_424_, v___x_425_);
v___x_427_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_eidx_398_ = stack[0].m_obj;
lean_object* v_e_399_ = stack[1].m_obj;
lean_object* v_a_400_ = stack[2].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(v_eidx_398_, v_e_399_, v_a_400_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object* v_eidx_431_, lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(v_eidx_431_, v_e_432_, v_a_433_);
return v_res_435_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object* v_ridx_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_recursorRuleMap_440_; lean_object* v___f_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
v_recursorRuleMap_440_ = lean_ctor_get(v_a_438_, 4);
v___f_441_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_442_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_437_);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_442_, v___f_441_, v_recursorRuleMap_440_, v_ridx_437_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_ridx_437_);
v_val_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_val_444_);
lean_ctor_set(v___x_448_, 1, v_a_438_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
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
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_443_);
lean_dec_ref(v_a_438_);
v___x_453_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0));
v___x_454_ = l_Nat_reprFast(v_ridx_437_);
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule_0interp(lean_interpreter_value* stack)
{
lean_object* v_ridx_437_ = stack[0].m_obj;
lean_object* v_a_438_ = stack[1].m_obj;
lean_object* v_res_458_;
v_res_458_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(v_ridx_437_, v_a_438_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object* v_ridx_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(v_ridx_459_, v_a_460_);
return v_res_462_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(lean_object* v_ridx_464_, lean_object* v_r_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_stream_468_; lean_object* v_nameMap_469_; lean_object* v_levelMap_470_; lean_object* v_exprMap_471_; lean_object* v_recursorRuleMap_472_; lean_object* v_constMap_473_; lean_object* v_constOrder_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_495_; 
v_stream_468_ = lean_ctor_get(v_a_466_, 0);
v_nameMap_469_ = lean_ctor_get(v_a_466_, 1);
v_levelMap_470_ = lean_ctor_get(v_a_466_, 2);
v_exprMap_471_ = lean_ctor_get(v_a_466_, 3);
v_recursorRuleMap_472_ = lean_ctor_get(v_a_466_, 4);
v_constMap_473_ = lean_ctor_get(v_a_466_, 5);
v_constOrder_474_ = lean_ctor_get(v_a_466_, 6);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_495_ == 0)
{
v___x_476_ = v_a_466_;
v_isShared_477_ = v_isSharedCheck_495_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_constOrder_474_);
lean_inc(v_constMap_473_);
lean_inc(v_recursorRuleMap_472_);
lean_inc(v_exprMap_471_);
lean_inc(v_levelMap_470_);
lean_inc(v_nameMap_469_);
lean_inc(v_stream_468_);
lean_dec(v_a_466_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_495_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___f_478_; lean_object* v___f_479_; uint8_t v___x_480_; 
v___f_478_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_479_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_464_);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_479_, v___f_478_, v_recursorRuleMap_472_, v_ridx_464_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_481_ = lean_box(0);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_479_, v___f_478_, v_recursorRuleMap_472_, v_ridx_464_, v_r_465_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_482_);
v___x_484_ = v___x_476_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_stream_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_nameMap_469_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_levelMap_470_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_exprMap_471_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_487_, 5, v_constMap_473_);
lean_ctor_set(v_reuseFailAlloc_487_, 6, v_constOrder_474_);
v___x_484_ = v_reuseFailAlloc_487_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_481_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_del_object(v___x_476_);
lean_dec_ref(v_constOrder_474_);
lean_dec_ref(v_constMap_473_);
lean_dec_ref(v_recursorRuleMap_472_);
lean_dec_ref(v_exprMap_471_);
lean_dec_ref(v_levelMap_470_);
lean_dec_ref(v_nameMap_469_);
lean_dec_ref(v_stream_468_);
lean_dec_ref(v_r_465_);
v___x_488_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___closed__0));
v___x_489_ = l_Nat_reprFast(v_ridx_464_);
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
v___x_493_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule_0interp(lean_interpreter_value* stack)
{
lean_object* v_ridx_464_ = stack[0].m_obj;
lean_object* v_r_465_ = stack[1].m_obj;
lean_object* v_a_466_ = stack[2].m_obj;
lean_object* v_res_496_;
v_res_496_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(v_ridx_464_, v_r_465_, v_a_466_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___boxed(lean_object* v_ridx_497_, lean_object* v_r_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(v_ridx_497_, v_r_498_, v_a_499_);
return v_res_501_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(lean_object* v_name_505_, lean_object* v_d_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_stream_509_; lean_object* v_nameMap_510_; lean_object* v_levelMap_511_; lean_object* v_exprMap_512_; lean_object* v_recursorRuleMap_513_; lean_object* v_constMap_514_; lean_object* v_constOrder_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_535_; 
v_stream_509_ = lean_ctor_get(v_a_507_, 0);
v_nameMap_510_ = lean_ctor_get(v_a_507_, 1);
v_levelMap_511_ = lean_ctor_get(v_a_507_, 2);
v_exprMap_512_ = lean_ctor_get(v_a_507_, 3);
v_recursorRuleMap_513_ = lean_ctor_get(v_a_507_, 4);
v_constMap_514_ = lean_ctor_get(v_a_507_, 5);
v_constOrder_515_ = lean_ctor_get(v_a_507_, 6);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_535_ == 0)
{
v___x_517_ = v_a_507_;
v_isShared_518_ = v_isSharedCheck_535_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_constOrder_515_);
lean_inc(v_constMap_514_);
lean_inc(v_recursorRuleMap_513_);
lean_inc(v_exprMap_512_);
lean_inc(v_levelMap_511_);
lean_inc(v_nameMap_510_);
lean_inc(v_stream_509_);
lean_dec(v_a_507_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_535_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0));
v___x_520_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1));
lean_inc(v_name_505_);
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_519_, v___x_520_, v_constMap_514_, v_name_505_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_box(0);
lean_inc(v_name_505_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_519_, v___x_520_, v_constMap_514_, v_name_505_, v_d_506_);
v___x_524_ = lean_array_push(v_constOrder_515_, v_name_505_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 6, v___x_524_);
lean_ctor_set(v___x_517_, 5, v___x_523_);
v___x_526_ = v___x_517_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_stream_509_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_nameMap_510_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_levelMap_511_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_exprMap_512_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_recursorRuleMap_513_);
lean_ctor_set(v_reuseFailAlloc_529_, 5, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_529_, 6, v___x_524_);
v___x_526_ = v_reuseFailAlloc_529_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_522_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_del_object(v___x_517_);
lean_dec_ref(v_constOrder_515_);
lean_dec_ref(v_constMap_514_);
lean_dec_ref(v_recursorRuleMap_513_);
lean_dec_ref(v_exprMap_512_);
lean_dec_ref(v_levelMap_511_);
lean_dec_ref(v_nameMap_510_);
lean_dec_ref(v_stream_509_);
lean_dec_ref(v_d_506_);
v___x_530_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_531_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_505_, v___x_521_);
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
lean_dec_ref(v___x_531_);
v___x_533_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_addConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_505_ = stack[0].m_obj;
lean_object* v_d_506_ = stack[1].m_obj;
lean_object* v_a_507_ = stack[2].m_obj;
lean_object* v_res_536_;
v_res_536_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(v_name_505_, v_d_506_, v_a_507_);
stack->m_obj
 = v_res_536_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___boxed(lean_object* v_name_537_, lean_object* v_d_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(v_name_537_, v_d_538_, v_a_539_);
return v_res_541_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(lean_object* v_line_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_LeanExport_Json_parse(v_line_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_a_547_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_560_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0));
v___x_555_ = lean_string_append(v___x_554_, v_a_550_);
lean_dec(v_a_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 18);
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_578_; 
v_a_561_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_578_ == 0)
{
v___x_563_ = v___x_549_;
v_isShared_564_ = v_isSharedCheck_578_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_549_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_578_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
if (lean_obj_tag(v_a_561_) == 5)
{
lean_object* v_kvPairs_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
lean_del_object(v___x_563_);
v_kvPairs_565_ = lean_ctor_get(v_a_561_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v_a_561_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_kvPairs_565_);
lean_dec(v_a_561_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_kvPairs_565_);
lean_ctor_set(v___x_569_, 1, v_a_547_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 0);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec(v_a_561_);
lean_dec_ref(v_a_547_);
v___x_574_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_574_);
v___x_576_ = v___x_563_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj_0interp(lean_interpreter_value* stack)
{
lean_object* v_line_546_ = stack[0].m_obj;
lean_object* v_a_547_ = stack[1].m_obj;
lean_object* v_res_579_;
v_res_579_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(v_line_546_, v_a_547_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___boxed(lean_object* v_line_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(v_line_580_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_box(0);
return v___x_586_;
}
else
{
lean_object* v_key_587_; lean_object* v_value_588_; lean_object* v_tail_589_; uint8_t v___x_590_; 
v_key_587_ = lean_ctor_get(v_x_585_, 0);
v_value_588_ = lean_ctor_get(v_x_585_, 1);
v_tail_589_ = lean_ctor_get(v_x_585_, 2);
v___x_590_ = lean_nat_dec_eq(v_key_587_, v_a_584_);
if (v___x_590_ == 0)
{
v_x_585_ = v_tail_589_;
goto _start;
}
else
{
lean_object* v___x_592_; 
lean_inc(v_value_588_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_value_588_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg___boxed(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec(v_a_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(lean_object* v_m_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_buckets_598_; lean_object* v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v_fold_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_buckets_598_ = lean_ctor_get(v_m_596_, 1);
v___x_599_ = lean_array_get_size(v_buckets_598_);
v___x_600_ = lean_uint64_of_nat(v_a_597_);
v___x_601_ = 32ULL;
v___x_602_ = lean_uint64_shift_right(v___x_600_, v___x_601_);
v_fold_603_ = lean_uint64_xor(v___x_600_, v___x_602_);
v___x_604_ = 16ULL;
v___x_605_ = lean_uint64_shift_right(v_fold_603_, v___x_604_);
v___x_606_ = lean_uint64_xor(v_fold_603_, v___x_605_);
v___x_607_ = lean_uint64_to_usize(v___x_606_);
v___x_608_ = lean_usize_of_nat(v___x_599_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v___x_608_, v___x_609_);
v___x_611_ = lean_usize_land(v___x_607_, v___x_610_);
v___x_612_ = lean_array_uget_borrowed(v_buckets_598_, v___x_611_);
v___x_613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_597_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg___boxed(lean_object* v_m_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_m_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(lean_object* v_t_617_, lean_object* v_k_618_){
_start:
{
if (lean_obj_tag(v_t_617_) == 0)
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v_l_621_; lean_object* v_r_622_; uint8_t v___x_623_; 
v_k_619_ = lean_ctor_get(v_t_617_, 1);
v_v_620_ = lean_ctor_get(v_t_617_, 2);
v_l_621_ = lean_ctor_get(v_t_617_, 3);
v_r_622_ = lean_ctor_get(v_t_617_, 4);
v___x_623_ = lean_string_compare(v_k_618_, v_k_619_);
switch(v___x_623_)
{
case 0:
{
v_t_617_ = v_l_621_;
goto _start;
}
case 1:
{
lean_object* v___x_625_; 
lean_inc(v_v_620_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v_v_620_);
return v___x_625_;
}
default: 
{
v_t_617_ = v_r_622_;
goto _start;
}
}
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg___boxed(lean_object* v_t_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_628_, v_k_629_);
lean_dec_ref(v_k_629_);
lean_dec(v_t_628_);
return v_res_630_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3(void){
_start:
{
lean_object* v_natZero_635_; lean_object* v_intZero_636_; 
v_natZero_635_ = lean_unsigned_to_nat(0u);
v_intZero_636_ = lean_nat_to_int(v_natZero_635_);
return v_intZero_636_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(lean_object* v_json_638_, lean_object* v_a_639_){
_start:
{
if (lean_obj_tag(v_json_638_) == 5)
{
lean_object* v_kvPairs_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_kvPairs_647_ = lean_ctor_get(v_json_638_, 0);
v___x_648_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_647_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
if (lean_obj_tag(v_val_650_) == 2)
{
lean_object* v_n_651_; lean_object* v_mantissa_652_; lean_object* v_exponent_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_697_; 
v_n_651_ = lean_ctor_get(v_val_650_, 0);
lean_inc_ref(v_n_651_);
lean_dec_ref_known(v_val_650_, 1);
v_mantissa_652_ = lean_ctor_get(v_n_651_, 0);
v_exponent_653_ = lean_ctor_get(v_n_651_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_n_651_);
if (v_isSharedCheck_697_ == 0)
{
v___x_655_ = v_n_651_;
v_isShared_656_ = v_isSharedCheck_697_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_exponent_653_);
lean_inc(v_mantissa_652_);
lean_dec(v_n_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_697_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_natZero_657_; lean_object* v_intZero_658_; uint8_t v_isNeg_659_; 
v_natZero_657_ = lean_unsigned_to_nat(0u);
v_intZero_658_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_659_ = lean_int_dec_lt(v_mantissa_652_, v_intZero_658_);
if (v_isNeg_659_ == 0)
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_eq(v_exponent_653_, v_natZero_657_);
lean_dec(v_exponent_653_);
if (v___x_660_ == 0)
{
lean_del_object(v___x_655_);
lean_dec(v_mantissa_652_);
lean_dec_ref(v_a_639_);
goto v___jp_641_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_647_, v___x_661_);
if (lean_obj_tag(v___x_662_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_696_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_696_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_696_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_696_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
if (lean_obj_tag(v_val_663_) == 3)
{
lean_object* v_s_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_695_; 
v_s_667_ = lean_ctor_get(v_val_663_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_val_663_);
if (v_isSharedCheck_695_ == 0)
{
v___x_669_ = v_val_663_;
v_isShared_670_ = v_isSharedCheck_695_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_s_667_);
lean_dec(v_val_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_695_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_nameMap_671_; lean_object* v_a_672_; lean_object* v___x_673_; 
v_nameMap_671_ = lean_ctor_get(v_a_639_, 1);
v_a_672_ = lean_nat_abs(v_mantissa_652_);
lean_dec(v_mantissa_652_);
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_671_, v_a_672_);
if (lean_obj_tag(v___x_673_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_a_672_);
lean_del_object(v___x_669_);
lean_del_object(v___x_665_);
v_val_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_685_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Name_str___override(v_val_674_, v_s_667_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_a_639_);
lean_ctor_set(v___x_655_, 0, v___x_678_);
v___x_680_ = v___x_655_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_a_639_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec(v___x_673_);
lean_dec_ref(v_s_667_);
lean_del_object(v___x_655_);
lean_dec_ref(v_a_639_);
v___x_686_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_687_ = l_Nat_reprFast(v_a_672_);
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
lean_dec_ref(v___x_687_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 18);
lean_ctor_set(v___x_669_, 0, v___x_688_);
v___x_690_ = v___x_669_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_690_);
v___x_692_ = v___x_665_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_del_object(v___x_665_);
lean_dec(v_val_663_);
lean_del_object(v___x_655_);
lean_dec(v_mantissa_652_);
lean_dec_ref(v_a_639_);
goto v___jp_644_;
}
}
}
else
{
lean_dec(v___x_662_);
lean_del_object(v___x_655_);
lean_dec(v_mantissa_652_);
lean_dec_ref(v_a_639_);
goto v___jp_644_;
}
}
}
else
{
lean_del_object(v___x_655_);
lean_dec(v_exponent_653_);
lean_dec(v_mantissa_652_);
lean_dec_ref(v_a_639_);
goto v___jp_641_;
}
}
}
else
{
lean_dec(v_val_650_);
lean_dec_ref(v_a_639_);
goto v___jp_641_;
}
}
else
{
lean_dec(v___x_649_);
lean_dec_ref(v_a_639_);
goto v___jp_641_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref(v_a_639_);
v___x_698_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_638_ = stack[0].m_obj;
lean_object* v_a_639_ = stack[1].m_obj;
lean_object* v_res_700_;
v_res_700_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_json_638_, v_a_639_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___boxed(lean_object* v_json_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_json_701_, v_a_702_);
lean_dec(v_json_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(lean_object* v_00_u03b4_705_, lean_object* v_t_706_, lean_object* v_k_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_706_, v_k_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___boxed(lean_object* v_00_u03b4_709_, lean_object* v_t_710_, lean_object* v_k_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(v_00_u03b4_709_, v_t_710_, v_k_711_);
lean_dec_ref(v_k_711_);
lean_dec(v_t_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(lean_object* v_00_u03b2_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_714_, v_a_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___boxed(lean_object* v_00_u03b2_717_, lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(v_00_u03b2_717_, v_m_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_m_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(lean_object* v_00_u03b2_721_, lean_object* v_a_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___boxed(lean_object* v_00_u03b2_725_, lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(v_00_u03b2_725_, v_a_726_, v_x_727_);
lean_dec(v_x_727_);
lean_dec(v_a_726_);
return v_res_728_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(lean_object* v_json_733_, lean_object* v_a_734_){
_start:
{
if (lean_obj_tag(v_json_733_) == 5)
{
lean_object* v_kvPairs_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_kvPairs_742_ = lean_ctor_get(v_json_733_, 0);
v___x_743_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_742_, v___x_743_);
if (lean_obj_tag(v___x_744_) == 1)
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_744_, 1);
if (lean_obj_tag(v_val_745_) == 2)
{
lean_object* v_n_746_; lean_object* v_mantissa_747_; lean_object* v_exponent_748_; lean_object* v_natZero_749_; lean_object* v_intZero_750_; uint8_t v_isNeg_751_; 
v_n_746_ = lean_ctor_get(v_val_745_, 0);
lean_inc_ref(v_n_746_);
lean_dec_ref_known(v_val_745_, 1);
v_mantissa_747_ = lean_ctor_get(v_n_746_, 0);
lean_inc(v_mantissa_747_);
v_exponent_748_ = lean_ctor_get(v_n_746_, 1);
lean_inc(v_exponent_748_);
lean_dec_ref(v_n_746_);
v_natZero_749_ = lean_unsigned_to_nat(0u);
v_intZero_750_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_751_ = lean_int_dec_lt(v_mantissa_747_, v_intZero_750_);
if (v_isNeg_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_eq(v_exponent_748_, v_natZero_749_);
lean_dec(v_exponent_748_);
if (v___x_752_ == 0)
{
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_736_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2));
v___x_754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_742_, v___x_753_);
if (lean_obj_tag(v___x_754_) == 1)
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_797_; 
v_val_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_797_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_797_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_797_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
if (lean_obj_tag(v_val_755_) == 2)
{
lean_object* v_n_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_796_; 
v_n_759_ = lean_ctor_get(v_val_755_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_val_755_);
if (v_isSharedCheck_796_ == 0)
{
v___x_761_ = v_val_755_;
v_isShared_762_ = v_isSharedCheck_796_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_n_759_);
lean_dec(v_val_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_796_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_mantissa_763_; lean_object* v_exponent_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_795_; 
v_mantissa_763_ = lean_ctor_get(v_n_759_, 0);
v_exponent_764_ = lean_ctor_get(v_n_759_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_n_759_);
if (v_isSharedCheck_795_ == 0)
{
v___x_766_ = v_n_759_;
v_isShared_767_ = v_isSharedCheck_795_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_exponent_764_);
lean_inc(v_mantissa_763_);
lean_dec(v_n_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_795_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v_isNeg_768_; 
v_isNeg_768_ = lean_int_dec_lt(v_mantissa_763_, v_intZero_750_);
if (v_isNeg_768_ == 0)
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_eq(v_exponent_764_, v_natZero_749_);
lean_dec(v_exponent_764_);
if (v___x_769_ == 0)
{
lean_del_object(v___x_766_);
lean_dec(v_mantissa_763_);
lean_del_object(v___x_761_);
lean_del_object(v___x_757_);
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_739_;
}
else
{
lean_object* v_nameMap_770_; lean_object* v_a_771_; lean_object* v___x_772_; 
v_nameMap_770_ = lean_ctor_get(v_a_734_, 1);
v_a_771_ = lean_nat_abs(v_mantissa_747_);
lean_dec(v_mantissa_747_);
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_770_, v_a_771_);
if (lean_obj_tag(v___x_772_) == 1)
{
lean_object* v_val_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_a_771_);
lean_del_object(v___x_761_);
lean_del_object(v___x_757_);
v_val_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_785_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_785_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_val_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_785_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v_a_777_ = lean_nat_abs(v_mantissa_763_);
lean_dec(v_mantissa_763_);
v___x_778_ = l_Lean_Name_num___override(v_val_773_, v_a_777_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_a_734_);
lean_ctor_set(v___x_766_, 0, v___x_778_);
v___x_780_ = v___x_766_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_734_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 0);
lean_ctor_set(v___x_775_, 0, v___x_780_);
v___x_782_ = v___x_775_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_dec(v___x_772_);
lean_del_object(v___x_766_);
lean_dec(v_mantissa_763_);
lean_dec_ref(v_a_734_);
v___x_786_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_787_ = l_Nat_reprFast(v_a_771_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 18);
lean_ctor_set(v___x_761_, 0, v___x_788_);
v___x_790_ = v___x_761_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_790_);
v___x_792_ = v___x_757_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_766_);
lean_dec(v_exponent_764_);
lean_dec(v_mantissa_763_);
lean_del_object(v___x_761_);
lean_del_object(v___x_757_);
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_739_;
}
}
}
}
else
{
lean_del_object(v___x_757_);
lean_dec(v_val_755_);
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_739_;
}
}
}
else
{
lean_dec(v___x_754_);
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_739_;
}
}
}
else
{
lean_dec(v_exponent_748_);
lean_dec(v_mantissa_747_);
lean_dec_ref(v_a_734_);
goto v___jp_736_;
}
}
else
{
lean_dec(v_val_745_);
lean_dec_ref(v_a_734_);
goto v___jp_736_;
}
}
else
{
lean_dec(v___x_744_);
lean_dec_ref(v_a_734_);
goto v___jp_736_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_a_734_);
v___x_798_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_733_ = stack[0].m_obj;
lean_object* v_a_734_ = stack[1].m_obj;
lean_object* v_res_800_;
v_res_800_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_json_733_, v_a_734_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___boxed(lean_object* v_json_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_json_801_, v_a_802_);
lean_dec(v_json_801_);
return v_res_804_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(lean_object* v_json_808_, lean_object* v_a_809_){
_start:
{
if (lean_obj_tag(v_json_808_) == 2)
{
lean_object* v_n_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_850_; 
v_n_814_ = lean_ctor_get(v_json_808_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_json_808_);
if (v_isSharedCheck_850_ == 0)
{
v___x_816_ = v_json_808_;
v_isShared_817_ = v_isSharedCheck_850_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_n_814_);
lean_dec(v_json_808_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_850_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_mantissa_818_; lean_object* v_exponent_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_849_; 
v_mantissa_818_ = lean_ctor_get(v_n_814_, 0);
v_exponent_819_ = lean_ctor_get(v_n_814_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_n_814_);
if (v_isSharedCheck_849_ == 0)
{
v___x_821_ = v_n_814_;
v_isShared_822_ = v_isSharedCheck_849_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_exponent_819_);
lean_inc(v_mantissa_818_);
lean_dec(v_n_814_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_849_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_natZero_823_; lean_object* v_intZero_824_; uint8_t v_isNeg_825_; 
v_natZero_823_ = lean_unsigned_to_nat(0u);
v_intZero_824_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_825_ = lean_int_dec_lt(v_mantissa_818_, v_intZero_824_);
if (v_isNeg_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = lean_nat_dec_eq(v_exponent_819_, v_natZero_823_);
lean_dec(v_exponent_819_);
if (v___x_826_ == 0)
{
lean_del_object(v___x_821_);
lean_dec(v_mantissa_818_);
lean_del_object(v___x_816_);
lean_dec_ref(v_a_809_);
goto v___jp_811_;
}
else
{
lean_object* v_levelMap_827_; lean_object* v_a_828_; lean_object* v___x_829_; 
v_levelMap_827_ = lean_ctor_get(v_a_809_, 2);
v_a_828_ = lean_nat_abs(v_mantissa_818_);
lean_dec(v_mantissa_818_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_827_, v_a_828_);
if (lean_obj_tag(v___x_829_) == 1)
{
lean_object* v_val_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_828_);
lean_del_object(v___x_816_);
v_val_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_841_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_val_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_Level_succ___override(v_val_830_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v_a_809_);
lean_ctor_set(v___x_821_, 0, v___x_834_);
v___x_836_ = v___x_821_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_809_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 0);
lean_ctor_set(v___x_832_, 0, v___x_836_);
v___x_838_ = v___x_832_;
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
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec(v___x_829_);
lean_del_object(v___x_821_);
lean_dec_ref(v_a_809_);
v___x_842_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_843_ = l_Nat_reprFast(v_a_828_);
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
lean_dec_ref(v___x_843_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 18);
lean_ctor_set(v___x_816_, 0, v___x_844_);
v___x_846_ = v___x_816_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
}
else
{
lean_del_object(v___x_821_);
lean_dec(v_exponent_819_);
lean_dec(v_mantissa_818_);
lean_del_object(v___x_816_);
lean_dec_ref(v_a_809_);
goto v___jp_811_;
}
}
}
}
else
{
lean_dec_ref(v_a_809_);
lean_dec(v_json_808_);
goto v___jp_811_;
}
v___jp_811_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1));
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_808_ = stack[0].m_obj;
lean_object* v_a_809_ = stack[1].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_json_808_, v_a_809_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___boxed(lean_object* v_json_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_json_852_, v_a_853_);
return v_res_855_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(lean_object* v_json_859_, lean_object* v_a_860_){
_start:
{
if (lean_obj_tag(v_json_859_) == 4)
{
lean_object* v_elems_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_elems_865_ = lean_ctor_get(v_json_859_, 0);
v___x_866_ = lean_array_get_size(v_elems_865_);
v___x_867_ = lean_unsigned_to_nat(2u);
v___x_868_ = lean_nat_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_array_fget(v_elems_865_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 2)
{
lean_object* v_n_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_935_; 
v_n_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_935_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_935_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_n_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_935_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_mantissa_875_; lean_object* v_exponent_876_; lean_object* v_intZero_877_; uint8_t v_isNeg_878_; 
v_mantissa_875_ = lean_ctor_get(v_n_871_, 0);
lean_inc(v_mantissa_875_);
v_exponent_876_ = lean_ctor_get(v_n_871_, 1);
lean_inc(v_exponent_876_);
lean_dec_ref(v_n_871_);
v_intZero_877_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_878_ = lean_int_dec_lt(v_mantissa_875_, v_intZero_877_);
if (v_isNeg_878_ == 0)
{
uint8_t v___x_879_; 
v___x_879_ = lean_nat_dec_eq(v_exponent_876_, v___x_869_);
lean_dec(v_exponent_876_);
if (v___x_879_ == 0)
{
lean_dec(v_mantissa_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_array_fget(v_elems_865_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 2)
{
lean_object* v_n_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_934_; 
v_n_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_934_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_934_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_n_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_934_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_mantissa_886_; lean_object* v_exponent_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_933_; 
v_mantissa_886_ = lean_ctor_get(v_n_882_, 0);
v_exponent_887_ = lean_ctor_get(v_n_882_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_n_882_);
if (v_isSharedCheck_933_ == 0)
{
v___x_889_ = v_n_882_;
v_isShared_890_ = v_isSharedCheck_933_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_exponent_887_);
lean_inc(v_mantissa_886_);
lean_dec(v_n_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_933_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v_isNeg_891_; 
v_isNeg_891_ = lean_int_dec_lt(v_mantissa_886_, v_intZero_877_);
if (v_isNeg_891_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = lean_nat_dec_eq(v_exponent_887_, v___x_869_);
lean_dec(v_exponent_887_);
if (v___x_892_ == 0)
{
lean_del_object(v___x_889_);
lean_dec(v_mantissa_886_);
lean_del_object(v___x_884_);
lean_dec(v_mantissa_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
else
{
lean_object* v_levelMap_893_; lean_object* v_a_894_; lean_object* v___x_895_; 
v_levelMap_893_ = lean_ctor_get(v_a_860_, 2);
v_a_894_ = lean_nat_abs(v_mantissa_875_);
lean_dec(v_mantissa_875_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_893_, v_a_894_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_894_);
lean_del_object(v___x_873_);
v_val_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_923_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_923_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_923_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_nat_abs(v_mantissa_886_);
lean_dec(v_mantissa_886_);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_893_, v_a_900_);
if (lean_obj_tag(v___x_901_) == 1)
{
lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_a_900_);
lean_del_object(v___x_898_);
lean_del_object(v___x_884_);
v_val_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lean_Level_max___override(v_val_896_, v_val_902_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_a_860_);
lean_ctor_set(v___x_889_, 0, v___x_906_);
v___x_908_ = v___x_889_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_860_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 0);
lean_ctor_set(v___x_904_, 0, v___x_908_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v___x_901_);
lean_dec(v_val_896_);
lean_del_object(v___x_889_);
lean_dec_ref(v_a_860_);
v___x_914_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_915_ = l_Nat_reprFast(v_a_900_);
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
lean_dec_ref(v___x_915_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 18);
lean_ctor_set(v___x_898_, 0, v___x_916_);
v___x_918_ = v___x_898_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 1);
lean_ctor_set(v___x_884_, 0, v___x_918_);
v___x_920_ = v___x_884_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v___x_895_);
lean_del_object(v___x_889_);
lean_dec(v_mantissa_886_);
lean_dec_ref(v_a_860_);
v___x_924_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_925_ = l_Nat_reprFast(v_a_894_);
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
lean_dec_ref(v___x_925_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 18);
lean_ctor_set(v___x_884_, 0, v___x_926_);
v___x_928_ = v___x_884_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 1);
lean_ctor_set(v___x_873_, 0, v___x_928_);
v___x_930_ = v___x_873_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_889_);
lean_dec(v_exponent_887_);
lean_dec(v_mantissa_886_);
lean_del_object(v___x_884_);
lean_dec(v_mantissa_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
}
}
}
else
{
lean_dec(v___x_881_);
lean_dec(v_mantissa_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
}
}
else
{
lean_dec(v_exponent_876_);
lean_dec(v_mantissa_875_);
lean_del_object(v___x_873_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
}
}
else
{
lean_dec(v___x_870_);
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
}
}
else
{
lean_dec_ref(v_a_860_);
goto v___jp_862_;
}
v___jp_862_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1));
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_859_ = stack[0].m_obj;
lean_object* v_a_860_ = stack[1].m_obj;
lean_object* v_res_936_;
v_res_936_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_json_859_, v_a_860_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___boxed(lean_object* v_json_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_json_937_, v_a_938_);
lean_dec(v_json_937_);
return v_res_940_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(lean_object* v_json_944_, lean_object* v_a_945_){
_start:
{
if (lean_obj_tag(v_json_944_) == 4)
{
lean_object* v_elems_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_elems_950_ = lean_ctor_get(v_json_944_, 0);
v___x_951_ = lean_array_get_size(v_elems_950_);
v___x_952_ = lean_unsigned_to_nat(2u);
v___x_953_ = lean_nat_dec_eq(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_array_fget(v_elems_950_, v___x_954_);
if (lean_obj_tag(v___x_955_) == 2)
{
lean_object* v_n_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1020_; 
v_n_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_1020_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_n_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1020_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_mantissa_960_; lean_object* v_exponent_961_; lean_object* v_intZero_962_; uint8_t v_isNeg_963_; 
v_mantissa_960_ = lean_ctor_get(v_n_956_, 0);
lean_inc(v_mantissa_960_);
v_exponent_961_ = lean_ctor_get(v_n_956_, 1);
lean_inc(v_exponent_961_);
lean_dec_ref(v_n_956_);
v_intZero_962_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_963_ = lean_int_dec_lt(v_mantissa_960_, v_intZero_962_);
if (v_isNeg_963_ == 0)
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_eq(v_exponent_961_, v___x_954_);
lean_dec(v_exponent_961_);
if (v___x_964_ == 0)
{
lean_dec(v_mantissa_960_);
lean_del_object(v___x_958_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_array_fget(v_elems_950_, v___x_965_);
if (lean_obj_tag(v___x_966_) == 2)
{
lean_object* v_n_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1019_; 
v_n_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_1019_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_n_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1019_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_mantissa_971_; lean_object* v_exponent_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1018_; 
v_mantissa_971_ = lean_ctor_get(v_n_967_, 0);
v_exponent_972_ = lean_ctor_get(v_n_967_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_n_967_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_974_ = v_n_967_;
v_isShared_975_ = v_isSharedCheck_1018_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_exponent_972_);
lean_inc(v_mantissa_971_);
lean_dec(v_n_967_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1018_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
uint8_t v_isNeg_976_; 
v_isNeg_976_ = lean_int_dec_lt(v_mantissa_971_, v_intZero_962_);
if (v_isNeg_976_ == 0)
{
uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_eq(v_exponent_972_, v___x_954_);
lean_dec(v_exponent_972_);
if (v___x_977_ == 0)
{
lean_del_object(v___x_974_);
lean_dec(v_mantissa_971_);
lean_del_object(v___x_969_);
lean_dec(v_mantissa_960_);
lean_del_object(v___x_958_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
else
{
lean_object* v_levelMap_978_; lean_object* v_a_979_; lean_object* v___x_980_; 
v_levelMap_978_ = lean_ctor_get(v_a_945_, 2);
v_a_979_ = lean_nat_abs(v_mantissa_960_);
lean_dec(v_mantissa_960_);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_978_, v_a_979_);
if (lean_obj_tag(v___x_980_) == 1)
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_979_);
lean_del_object(v___x_958_);
v_val_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1008_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1008_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_nat_abs(v_mantissa_971_);
lean_dec(v_mantissa_971_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_978_, v_a_985_);
if (lean_obj_tag(v___x_986_) == 1)
{
lean_object* v_val_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_985_);
lean_del_object(v___x_983_);
lean_del_object(v___x_969_);
v_val_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_998_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_val_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_Level_imax___override(v_val_981_, v_val_987_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_a_945_);
lean_ctor_set(v___x_974_, 0, v___x_991_);
v___x_993_ = v___x_974_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_945_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 0, v___x_993_);
v___x_995_ = v___x_989_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec(v___x_986_);
lean_dec(v_val_981_);
lean_del_object(v___x_974_);
lean_dec_ref(v_a_945_);
v___x_999_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1000_ = l_Nat_reprFast(v_a_985_);
v___x_1001_ = lean_string_append(v___x_999_, v___x_1000_);
lean_dec_ref(v___x_1000_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 18);
lean_ctor_set(v___x_983_, 0, v___x_1001_);
v___x_1003_ = v___x_983_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 1);
lean_ctor_set(v___x_969_, 0, v___x_1003_);
v___x_1005_ = v___x_969_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v___x_980_);
lean_del_object(v___x_974_);
lean_dec(v_mantissa_971_);
lean_dec_ref(v_a_945_);
v___x_1009_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1010_ = l_Nat_reprFast(v_a_979_);
v___x_1011_ = lean_string_append(v___x_1009_, v___x_1010_);
lean_dec_ref(v___x_1010_);
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 18);
lean_ctor_set(v___x_969_, 0, v___x_1011_);
v___x_1013_ = v___x_969_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 0, v___x_1013_);
v___x_1015_ = v___x_958_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_del_object(v___x_974_);
lean_dec(v_exponent_972_);
lean_dec(v_mantissa_971_);
lean_del_object(v___x_969_);
lean_dec(v_mantissa_960_);
lean_del_object(v___x_958_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
}
}
}
else
{
lean_dec(v___x_966_);
lean_dec(v_mantissa_960_);
lean_del_object(v___x_958_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
}
}
else
{
lean_dec(v_exponent_961_);
lean_dec(v_mantissa_960_);
lean_del_object(v___x_958_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
}
}
else
{
lean_dec(v___x_955_);
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
}
}
else
{
lean_dec_ref(v_a_945_);
goto v___jp_947_;
}
v___jp_947_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1));
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_944_ = stack[0].m_obj;
lean_object* v_a_945_ = stack[1].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_json_944_, v_a_945_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___boxed(lean_object* v_json_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_json_1022_, v_a_1023_);
lean_dec(v_json_1022_);
return v_res_1025_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(lean_object* v_json_1029_, lean_object* v_a_1030_){
_start:
{
if (lean_obj_tag(v_json_1029_) == 2)
{
lean_object* v_n_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1071_; 
v_n_1035_ = lean_ctor_get(v_json_1029_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_json_1029_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1037_ = v_json_1029_;
v_isShared_1038_ = v_isSharedCheck_1071_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_n_1035_);
lean_dec(v_json_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1071_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_mantissa_1039_; lean_object* v_exponent_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1070_; 
v_mantissa_1039_ = lean_ctor_get(v_n_1035_, 0);
v_exponent_1040_ = lean_ctor_get(v_n_1035_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_n_1035_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1042_ = v_n_1035_;
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_exponent_1040_);
lean_inc(v_mantissa_1039_);
lean_dec(v_n_1035_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_natZero_1044_; lean_object* v_intZero_1045_; uint8_t v_isNeg_1046_; 
v_natZero_1044_ = lean_unsigned_to_nat(0u);
v_intZero_1045_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1046_ = lean_int_dec_lt(v_mantissa_1039_, v_intZero_1045_);
if (v_isNeg_1046_ == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_nat_dec_eq(v_exponent_1040_, v_natZero_1044_);
lean_dec(v_exponent_1040_);
if (v___x_1047_ == 0)
{
lean_del_object(v___x_1042_);
lean_dec(v_mantissa_1039_);
lean_del_object(v___x_1037_);
lean_dec_ref(v_a_1030_);
goto v___jp_1032_;
}
else
{
lean_object* v_nameMap_1048_; lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_nameMap_1048_ = lean_ctor_get(v_a_1030_, 1);
v_a_1049_ = lean_nat_abs(v_mantissa_1039_);
lean_dec(v_mantissa_1039_);
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1050_) == 1)
{
lean_object* v_val_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1049_);
lean_del_object(v___x_1037_);
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_val_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = l_Lean_Level_param___override(v_val_1051_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v_a_1030_);
lean_ctor_set(v___x_1042_, 0, v___x_1055_);
v___x_1057_ = v___x_1042_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_a_1030_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec(v___x_1050_);
lean_del_object(v___x_1042_);
lean_dec_ref(v_a_1030_);
v___x_1063_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1064_ = l_Nat_reprFast(v_a_1049_);
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
lean_dec_ref(v___x_1064_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 18);
lean_ctor_set(v___x_1037_, 0, v___x_1065_);
v___x_1067_ = v___x_1037_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
}
}
else
{
lean_del_object(v___x_1042_);
lean_dec(v_exponent_1040_);
lean_dec(v_mantissa_1039_);
lean_del_object(v___x_1037_);
lean_dec_ref(v_a_1030_);
goto v___jp_1032_;
}
}
}
}
else
{
lean_dec_ref(v_a_1030_);
lean_dec(v_json_1029_);
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1));
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1029_ = stack[0].m_obj;
lean_object* v_a_1030_ = stack[1].m_obj;
lean_object* v_res_1072_;
v_res_1072_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_json_1029_, v_a_1030_);
stack->m_obj
 = v_res_1072_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___boxed(lean_object* v_json_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_json_1073_, v_a_1074_);
return v_res_1076_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(lean_object* v_json_1080_, lean_object* v_a_1081_){
_start:
{
if (lean_obj_tag(v_json_1080_) == 2)
{
lean_object* v_n_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1108_; 
v_n_1086_ = lean_ctor_get(v_json_1080_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_json_1080_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1088_ = v_json_1080_;
v_isShared_1089_ = v_isSharedCheck_1108_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_n_1086_);
lean_dec(v_json_1080_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1108_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_mantissa_1090_; lean_object* v_exponent_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1107_; 
v_mantissa_1090_ = lean_ctor_get(v_n_1086_, 0);
v_exponent_1091_ = lean_ctor_get(v_n_1086_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_n_1086_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1093_ = v_n_1086_;
v_isShared_1094_ = v_isSharedCheck_1107_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_exponent_1091_);
lean_inc(v_mantissa_1090_);
lean_dec(v_n_1086_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1107_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_natZero_1095_; lean_object* v_intZero_1096_; uint8_t v_isNeg_1097_; 
v_natZero_1095_ = lean_unsigned_to_nat(0u);
v_intZero_1096_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1097_ = lean_int_dec_lt(v_mantissa_1090_, v_intZero_1096_);
if (v_isNeg_1097_ == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_eq(v_exponent_1091_, v_natZero_1095_);
lean_dec(v_exponent_1091_);
if (v___x_1098_ == 0)
{
lean_del_object(v___x_1093_);
lean_dec(v_mantissa_1090_);
lean_del_object(v___x_1088_);
lean_dec_ref(v_a_1081_);
goto v___jp_1083_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v_a_1099_ = lean_nat_abs(v_mantissa_1090_);
lean_dec(v_mantissa_1090_);
v___x_1100_ = l_Lean_Expr_bvar___override(v_a_1099_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_a_1081_);
lean_ctor_set(v___x_1093_, 0, v___x_1100_);
v___x_1102_ = v___x_1093_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_1081_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1102_);
v___x_1104_ = v___x_1088_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_del_object(v___x_1093_);
lean_dec(v_exponent_1091_);
lean_dec(v_mantissa_1090_);
lean_del_object(v___x_1088_);
lean_dec_ref(v_a_1081_);
goto v___jp_1083_;
}
}
}
}
else
{
lean_dec_ref(v_a_1081_);
lean_dec(v_json_1080_);
goto v___jp_1083_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1));
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1080_ = stack[0].m_obj;
lean_object* v_a_1081_ = stack[1].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_json_1080_, v_a_1081_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___boxed(lean_object* v_json_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_json_1110_, v_a_1111_);
return v_res_1113_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(lean_object* v_json_1117_, lean_object* v_a_1118_){
_start:
{
if (lean_obj_tag(v_json_1117_) == 2)
{
lean_object* v_n_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1159_; 
v_n_1123_ = lean_ctor_get(v_json_1117_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_json_1117_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1125_ = v_json_1117_;
v_isShared_1126_ = v_isSharedCheck_1159_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_n_1123_);
lean_dec(v_json_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1159_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_mantissa_1127_; lean_object* v_exponent_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1158_; 
v_mantissa_1127_ = lean_ctor_get(v_n_1123_, 0);
v_exponent_1128_ = lean_ctor_get(v_n_1123_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_n_1123_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1130_ = v_n_1123_;
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_exponent_1128_);
lean_inc(v_mantissa_1127_);
lean_dec(v_n_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_natZero_1132_; lean_object* v_intZero_1133_; uint8_t v_isNeg_1134_; 
v_natZero_1132_ = lean_unsigned_to_nat(0u);
v_intZero_1133_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1134_ = lean_int_dec_lt(v_mantissa_1127_, v_intZero_1133_);
if (v_isNeg_1134_ == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_nat_dec_eq(v_exponent_1128_, v_natZero_1132_);
lean_dec(v_exponent_1128_);
if (v___x_1135_ == 0)
{
lean_del_object(v___x_1130_);
lean_dec(v_mantissa_1127_);
lean_del_object(v___x_1125_);
lean_dec_ref(v_a_1118_);
goto v___jp_1120_;
}
else
{
lean_object* v_levelMap_1136_; lean_object* v_a_1137_; lean_object* v___x_1138_; 
v_levelMap_1136_ = lean_ctor_get(v_a_1118_, 2);
v_a_1137_ = lean_nat_abs(v_mantissa_1127_);
lean_dec(v_mantissa_1127_);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1138_) == 1)
{
lean_object* v_val_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1137_);
lean_del_object(v___x_1125_);
v_val_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1150_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_val_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1150_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = l_Lean_Expr_sort___override(v_val_1139_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v_a_1118_);
lean_ctor_set(v___x_1130_, 0, v___x_1143_);
v___x_1145_ = v___x_1130_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1118_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1147_ = v___x_1141_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v___x_1138_);
lean_del_object(v___x_1130_);
lean_dec_ref(v_a_1118_);
v___x_1151_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1152_ = l_Nat_reprFast(v_a_1137_);
v___x_1153_ = lean_string_append(v___x_1151_, v___x_1152_);
lean_dec_ref(v___x_1152_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 18);
lean_ctor_set(v___x_1125_, 0, v___x_1153_);
v___x_1155_ = v___x_1125_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
}
else
{
lean_del_object(v___x_1130_);
lean_dec(v_exponent_1128_);
lean_dec(v_mantissa_1127_);
lean_del_object(v___x_1125_);
lean_dec_ref(v_a_1118_);
goto v___jp_1120_;
}
}
}
}
else
{
lean_dec_ref(v_a_1118_);
lean_dec(v_json_1117_);
goto v___jp_1120_;
}
v___jp_1120_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1));
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1117_ = stack[0].m_obj;
lean_object* v_a_1118_ = stack[1].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_json_1117_, v_a_1118_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___boxed(lean_object* v_json_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_json_1161_, v_a_1162_);
return v_res_1164_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_bs_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_bs_1170_);
lean_ctor_set(v___x_1177_, 1, v___y_1171_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v_v_1179_; 
v_v_1179_ = lean_array_uget(v_bs_1170_, v_i_1169_);
if (lean_obj_tag(v_v_1179_) == 2)
{
lean_object* v_n_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1206_; 
v_n_1180_ = lean_ctor_get(v_v_1179_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_v_1179_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1182_ = v_v_1179_;
v_isShared_1183_ = v_isSharedCheck_1206_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_n_1180_);
lean_dec(v_v_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1206_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_mantissa_1184_; lean_object* v_exponent_1185_; lean_object* v_natZero_1186_; lean_object* v_intZero_1187_; uint8_t v_isNeg_1188_; 
v_mantissa_1184_ = lean_ctor_get(v_n_1180_, 0);
lean_inc(v_mantissa_1184_);
v_exponent_1185_ = lean_ctor_get(v_n_1180_, 1);
lean_inc(v_exponent_1185_);
lean_dec_ref(v_n_1180_);
v_natZero_1186_ = lean_unsigned_to_nat(0u);
v_intZero_1187_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1188_ = lean_int_dec_lt(v_mantissa_1184_, v_intZero_1187_);
if (v_isNeg_1188_ == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_eq(v_exponent_1185_, v_natZero_1186_);
lean_dec(v_exponent_1185_);
if (v___x_1189_ == 0)
{
lean_dec(v_mantissa_1184_);
lean_del_object(v___x_1182_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_bs_1170_);
goto v___jp_1173_;
}
else
{
lean_object* v_levelMap_1190_; lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_levelMap_1190_ = lean_ctor_get(v___y_1171_, 2);
v_a_1191_ = lean_nat_abs(v_mantissa_1184_);
lean_dec(v_mantissa_1184_);
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1192_) == 1)
{
lean_object* v_val_1193_; lean_object* v_bs_x27_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_a_1191_);
lean_del_object(v___x_1182_);
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v_bs_x27_1194_ = lean_array_uset(v_bs_1170_, v_i_1169_, v_natZero_1186_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_i_1169_, v___x_1195_);
v___x_1197_ = lean_array_uset(v_bs_x27_1194_, v_i_1169_, v_val_1193_);
v_i_1169_ = v___x_1196_;
v_bs_1170_ = v___x_1197_;
goto _start;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v___x_1192_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_bs_1170_);
v___x_1199_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1200_ = l_Nat_reprFast(v_a_1191_);
v___x_1201_ = lean_string_append(v___x_1199_, v___x_1200_);
lean_dec_ref(v___x_1200_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 18);
lean_ctor_set(v___x_1182_, 0, v___x_1201_);
v___x_1203_ = v___x_1182_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
}
else
{
lean_dec(v_exponent_1185_);
lean_dec(v_mantissa_1184_);
lean_del_object(v___x_1182_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_bs_1170_);
goto v___jp_1173_;
}
}
}
else
{
lean_dec(v_v_1179_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_bs_1170_);
goto v___jp_1173_;
}
}
v___jp_1173_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1168_ = stack[0].m_num;
size_t v_i_1169_ = stack[1].m_num;
lean_object* v_bs_1170_ = stack[2].m_obj;
lean_object* v___y_1171_ = stack[3].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_1168_, v_i_1169_, v_bs_1170_, v___y_1171_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___boxed(lean_object* v_sz_1208_, lean_object* v_i_1209_, lean_object* v_bs_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
size_t v_sz_boxed_1213_; size_t v_i_boxed_1214_; lean_object* v_res_1215_; 
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1208_);
lean_dec(v_sz_1208_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_boxed_1213_, v_i_boxed_1214_, v_bs_1210_, v___y_1211_);
return v_res_1215_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(lean_object* v_json_1218_, lean_object* v_a_1219_){
_start:
{
if (lean_obj_tag(v_json_1218_) == 5)
{
lean_object* v_kvPairs_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_kvPairs_1227_ = lean_ctor_get(v_json_1218_, 0);
v___x_1228_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1227_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
if (lean_obj_tag(v_val_1230_) == 2)
{
lean_object* v_n_1231_; lean_object* v_mantissa_1232_; lean_object* v_exponent_1233_; lean_object* v_natZero_1234_; lean_object* v_intZero_1235_; uint8_t v_isNeg_1236_; 
v_n_1231_ = lean_ctor_get(v_val_1230_, 0);
lean_inc_ref(v_n_1231_);
lean_dec_ref_known(v_val_1230_, 1);
v_mantissa_1232_ = lean_ctor_get(v_n_1231_, 0);
lean_inc(v_mantissa_1232_);
v_exponent_1233_ = lean_ctor_get(v_n_1231_, 1);
lean_inc(v_exponent_1233_);
lean_dec_ref(v_n_1231_);
v_natZero_1234_ = lean_unsigned_to_nat(0u);
v_intZero_1235_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1236_ = lean_int_dec_lt(v_mantissa_1232_, v_intZero_1235_);
if (v_isNeg_1236_ == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_nat_dec_eq(v_exponent_1233_, v_natZero_1234_);
lean_dec(v_exponent_1233_);
if (v___x_1237_ == 0)
{
lean_dec(v_mantissa_1232_);
lean_dec_ref(v_a_1219_);
goto v___jp_1221_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1));
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1227_, v___x_1238_);
if (lean_obj_tag(v___x_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1292_; 
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1292_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_val_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1292_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_val_1240_) == 4)
{
lean_object* v_elems_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1291_; 
v_elems_1244_ = lean_ctor_get(v_val_1240_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_val_1240_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1246_ = v_val_1240_;
v_isShared_1247_ = v_isSharedCheck_1291_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_elems_1244_);
lean_dec(v_val_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1291_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_nameMap_1248_; lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_nameMap_1248_ = lean_ctor_get(v_a_1219_, 1);
v_a_1249_ = lean_nat_abs(v_mantissa_1232_);
lean_dec(v_mantissa_1232_);
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_val_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_a_1249_);
lean_del_object(v___x_1246_);
lean_del_object(v___x_1242_);
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_sz_1252_ = lean_array_size(v_elems_1244_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_1252_, v___x_1253_, v_elems_1244_, v_a_1219_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1273_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1273_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1273_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1272_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
v_snd_1260_ = lean_ctor_get(v_a_1255_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1262_ = v_a_1255_;
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_inc(v_fst_1259_);
lean_dec(v_a_1255_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1264_ = lean_array_to_list(v_fst_1259_);
v___x_1265_ = l_Lean_Expr_const___override(v_val_1251_, v___x_1264_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1265_);
v___x_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_snd_1260_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1267_);
v___x_1269_ = v___x_1257_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_val_1251_);
v_a_1274_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1254_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1254_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec(v___x_1250_);
lean_dec_ref(v_elems_1244_);
lean_dec_ref(v_a_1219_);
v___x_1282_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1283_ = l_Nat_reprFast(v_a_1249_);
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
lean_dec_ref(v___x_1283_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 18);
lean_ctor_set(v___x_1246_, 0, v___x_1284_);
v___x_1286_ = v___x_1246_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1286_);
v___x_1288_ = v___x_1242_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_del_object(v___x_1242_);
lean_dec(v_val_1240_);
lean_dec(v_mantissa_1232_);
lean_dec_ref(v_a_1219_);
goto v___jp_1224_;
}
}
}
else
{
lean_dec(v___x_1239_);
lean_dec(v_mantissa_1232_);
lean_dec_ref(v_a_1219_);
goto v___jp_1224_;
}
}
}
else
{
lean_dec(v_exponent_1233_);
lean_dec(v_mantissa_1232_);
lean_dec_ref(v_a_1219_);
goto v___jp_1221_;
}
}
else
{
lean_dec(v_val_1230_);
lean_dec_ref(v_a_1219_);
goto v___jp_1221_;
}
}
else
{
lean_dec(v___x_1229_);
lean_dec_ref(v_a_1219_);
goto v___jp_1221_;
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v_a_1219_);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
v___jp_1221_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1218_ = stack[0].m_obj;
lean_object* v_a_1219_ = stack[1].m_obj;
lean_object* v_res_1295_;
v_res_1295_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_json_1218_, v_a_1219_);
stack->m_obj
 = v_res_1295_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___boxed(lean_object* v_json_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_json_1296_, v_a_1297_);
lean_dec(v_json_1296_);
return v_res_1299_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(lean_object* v_json_1305_, lean_object* v_a_1306_){
_start:
{
if (lean_obj_tag(v_json_1305_) == 5)
{
lean_object* v_kvPairs_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_kvPairs_1314_ = lean_ctor_get(v_json_1305_, 0);
v___x_1315_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2));
v___x_1316_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1314_, v___x_1315_);
if (lean_obj_tag(v___x_1316_) == 1)
{
lean_object* v_val_1317_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1316_, 1);
if (lean_obj_tag(v_val_1317_) == 2)
{
lean_object* v_n_1318_; lean_object* v_mantissa_1319_; lean_object* v_exponent_1320_; lean_object* v_natZero_1321_; lean_object* v_intZero_1322_; uint8_t v_isNeg_1323_; 
v_n_1318_ = lean_ctor_get(v_val_1317_, 0);
lean_inc_ref(v_n_1318_);
lean_dec_ref_known(v_val_1317_, 1);
v_mantissa_1319_ = lean_ctor_get(v_n_1318_, 0);
lean_inc(v_mantissa_1319_);
v_exponent_1320_ = lean_ctor_get(v_n_1318_, 1);
lean_inc(v_exponent_1320_);
lean_dec_ref(v_n_1318_);
v_natZero_1321_ = lean_unsigned_to_nat(0u);
v_intZero_1322_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1323_ = lean_int_dec_lt(v_mantissa_1319_, v_intZero_1322_);
if (v_isNeg_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_nat_dec_eq(v_exponent_1320_, v_natZero_1321_);
lean_dec(v_exponent_1320_);
if (v___x_1324_ == 0)
{
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1308_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3));
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1314_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 1)
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1384_; 
v_val_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1384_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1384_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
if (lean_obj_tag(v_val_1327_) == 2)
{
lean_object* v_n_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1383_; 
v_n_1331_ = lean_ctor_get(v_val_1327_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_val_1327_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1333_ = v_val_1327_;
v_isShared_1334_ = v_isSharedCheck_1383_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_n_1331_);
lean_dec(v_val_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1383_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_mantissa_1335_; lean_object* v_exponent_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1382_; 
v_mantissa_1335_ = lean_ctor_get(v_n_1331_, 0);
v_exponent_1336_ = lean_ctor_get(v_n_1331_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_n_1331_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1338_ = v_n_1331_;
v_isShared_1339_ = v_isSharedCheck_1382_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_exponent_1336_);
lean_inc(v_mantissa_1335_);
lean_dec(v_n_1331_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1382_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v_isNeg_1340_; 
v_isNeg_1340_ = lean_int_dec_lt(v_mantissa_1335_, v_intZero_1322_);
if (v_isNeg_1340_ == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_nat_dec_eq(v_exponent_1336_, v_natZero_1321_);
lean_dec(v_exponent_1336_);
if (v___x_1341_ == 0)
{
lean_del_object(v___x_1338_);
lean_dec(v_mantissa_1335_);
lean_del_object(v___x_1333_);
lean_del_object(v___x_1329_);
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1311_;
}
else
{
lean_object* v_exprMap_1342_; lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_exprMap_1342_ = lean_ctor_get(v_a_1306_, 3);
v_a_1343_ = lean_nat_abs(v_mantissa_1319_);
lean_dec(v_mantissa_1319_);
v___x_1344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1342_, v_a_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_a_1343_);
lean_del_object(v___x_1329_);
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1372_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_val_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1372_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_nat_abs(v_mantissa_1335_);
lean_dec(v_mantissa_1335_);
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1342_, v_a_1349_);
if (lean_obj_tag(v___x_1350_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1349_);
lean_del_object(v___x_1347_);
lean_del_object(v___x_1333_);
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l_Lean_Expr_app___override(v_val_1345_, v_val_1351_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_a_1306_);
lean_ctor_set(v___x_1338_, 0, v___x_1355_);
v___x_1357_ = v___x_1338_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_a_1306_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1357_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v___x_1350_);
lean_dec(v_val_1345_);
lean_del_object(v___x_1338_);
lean_dec_ref(v_a_1306_);
v___x_1363_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1364_ = l_Nat_reprFast(v_a_1349_);
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
lean_dec_ref(v___x_1364_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 18);
lean_ctor_set(v___x_1347_, 0, v___x_1365_);
v___x_1367_ = v___x_1347_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1367_);
v___x_1369_ = v___x_1333_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v___x_1344_);
lean_del_object(v___x_1338_);
lean_dec(v_mantissa_1335_);
lean_dec_ref(v_a_1306_);
v___x_1373_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1374_ = l_Nat_reprFast(v_a_1343_);
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
lean_dec_ref(v___x_1374_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 18);
lean_ctor_set(v___x_1333_, 0, v___x_1375_);
v___x_1377_ = v___x_1333_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1377_);
v___x_1379_ = v___x_1329_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
lean_del_object(v___x_1338_);
lean_dec(v_exponent_1336_);
lean_dec(v_mantissa_1335_);
lean_del_object(v___x_1333_);
lean_del_object(v___x_1329_);
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1311_;
}
}
}
}
else
{
lean_del_object(v___x_1329_);
lean_dec(v_val_1327_);
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1311_;
}
}
}
else
{
lean_dec(v___x_1326_);
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1311_;
}
}
}
else
{
lean_dec(v_exponent_1320_);
lean_dec(v_mantissa_1319_);
lean_dec_ref(v_a_1306_);
goto v___jp_1308_;
}
}
else
{
lean_dec(v_val_1317_);
lean_dec_ref(v_a_1306_);
goto v___jp_1308_;
}
}
else
{
lean_dec(v___x_1316_);
lean_dec_ref(v_a_1306_);
goto v___jp_1308_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v_a_1306_);
v___x_1385_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1305_ = stack[0].m_obj;
lean_object* v_a_1306_ = stack[1].m_obj;
lean_object* v_res_1387_;
v_res_1387_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_json_1305_, v_a_1306_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___boxed(lean_object* v_json_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_json_1388_, v_a_1389_);
lean_dec(v_json_1388_);
return v_res_1391_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(lean_object* v_info_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0));
v___x_1401_ = lean_string_dec_eq(v_info_1397_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1));
v___x_1403_ = lean_string_dec_eq(v_info_1397_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2));
v___x_1405_ = lean_string_dec_eq(v_info_1397_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3));
v___x_1407_ = lean_string_dec_eq(v_info_1397_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref(v_a_1398_);
v___x_1408_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4));
v___x_1409_ = lean_string_append(v___x_1408_, v_info_1397_);
v___x_1410_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = 3;
v___x_1413_ = lean_box(v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1398_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
else
{
uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = 2;
v___x_1417_ = lean_box(v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_a_1398_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
else
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = 1;
v___x_1421_ = lean_box(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v_a_1398_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
else
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_a_1398_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1397_ = stack[0].m_obj;
lean_object* v_a_1398_ = stack[1].m_obj;
lean_object* v_res_1428_;
v_res_1428_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_info_1397_, v_a_1398_);
stack->m_obj
 = v_res_1428_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___boxed(lean_object* v_info_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_info_1429_, v_a_1430_);
lean_dec_ref(v_info_1429_);
return v_res_1432_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(lean_object* v_json_1439_, lean_object* v_a_1440_){
_start:
{
if (lean_obj_tag(v_json_1439_) == 5)
{
lean_object* v_kvPairs_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_kvPairs_1454_ = lean_ctor_get(v_json_1439_, 0);
v___x_1455_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1454_, v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 1)
{
lean_object* v_val_1457_; 
v_val_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___x_1456_, 1);
if (lean_obj_tag(v_val_1457_) == 2)
{
lean_object* v_n_1458_; lean_object* v_mantissa_1459_; lean_object* v_exponent_1460_; lean_object* v_natZero_1461_; lean_object* v_intZero_1462_; uint8_t v_isNeg_1463_; 
v_n_1458_ = lean_ctor_get(v_val_1457_, 0);
lean_inc_ref(v_n_1458_);
lean_dec_ref_known(v_val_1457_, 1);
v_mantissa_1459_ = lean_ctor_get(v_n_1458_, 0);
lean_inc(v_mantissa_1459_);
v_exponent_1460_ = lean_ctor_get(v_n_1458_, 1);
lean_inc(v_exponent_1460_);
lean_dec_ref(v_n_1458_);
v_natZero_1461_ = lean_unsigned_to_nat(0u);
v_intZero_1462_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1463_ = lean_int_dec_lt(v_mantissa_1459_, v_intZero_1462_);
if (v_isNeg_1463_ == 0)
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_eq(v_exponent_1460_, v_natZero_1461_);
lean_dec(v_exponent_1460_);
if (v___x_1464_ == 0)
{
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1442_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1454_, v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 1)
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v___x_1466_, 1);
if (lean_obj_tag(v_val_1467_) == 2)
{
lean_object* v_n_1468_; lean_object* v_mantissa_1469_; lean_object* v_exponent_1470_; uint8_t v_isNeg_1471_; 
v_n_1468_ = lean_ctor_get(v_val_1467_, 0);
lean_inc_ref(v_n_1468_);
lean_dec_ref_known(v_val_1467_, 1);
v_mantissa_1469_ = lean_ctor_get(v_n_1468_, 0);
lean_inc(v_mantissa_1469_);
v_exponent_1470_ = lean_ctor_get(v_n_1468_, 1);
lean_inc(v_exponent_1470_);
lean_dec_ref(v_n_1468_);
v_isNeg_1471_ = lean_int_dec_lt(v_mantissa_1469_, v_intZero_1462_);
if (v_isNeg_1471_ == 0)
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_nat_dec_eq(v_exponent_1470_, v_natZero_1461_);
lean_dec(v_exponent_1470_);
if (v___x_1472_ == 0)
{
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1445_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1474_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1454_, v___x_1473_);
if (lean_obj_tag(v___x_1474_) == 1)
{
lean_object* v_val_1475_; 
v_val_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___x_1474_, 1);
if (lean_obj_tag(v_val_1475_) == 2)
{
lean_object* v_n_1476_; lean_object* v_mantissa_1477_; lean_object* v_exponent_1478_; uint8_t v_isNeg_1479_; 
v_n_1476_ = lean_ctor_get(v_val_1475_, 0);
lean_inc_ref(v_n_1476_);
lean_dec_ref_known(v_val_1475_, 1);
v_mantissa_1477_ = lean_ctor_get(v_n_1476_, 0);
lean_inc(v_mantissa_1477_);
v_exponent_1478_ = lean_ctor_get(v_n_1476_, 1);
lean_inc(v_exponent_1478_);
lean_dec_ref(v_n_1476_);
v_isNeg_1479_ = lean_int_dec_lt(v_mantissa_1477_, v_intZero_1462_);
if (v_isNeg_1479_ == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_nat_dec_eq(v_exponent_1478_, v_natZero_1461_);
lean_dec(v_exponent_1478_);
if (v___x_1480_ == 0)
{
lean_dec(v_mantissa_1477_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1448_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1454_, v___x_1481_);
if (lean_obj_tag(v___x_1482_) == 1)
{
lean_object* v_val_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1566_; 
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1566_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_val_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1566_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
if (lean_obj_tag(v_val_1483_) == 3)
{
lean_object* v_s_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1565_; 
v_s_1487_ = lean_ctor_get(v_val_1483_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_val_1483_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1489_ = v_val_1483_;
v_isShared_1490_ = v_isSharedCheck_1565_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_s_1487_);
lean_dec(v_val_1483_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1565_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_nameMap_1491_; lean_object* v_exprMap_1492_; lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_nameMap_1491_ = lean_ctor_get(v_a_1440_, 1);
v_exprMap_1492_ = lean_ctor_get(v_a_1440_, 3);
v_a_1493_ = lean_nat_abs(v_mantissa_1459_);
lean_dec(v_mantissa_1459_);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1491_, v_a_1493_);
if (lean_obj_tag(v___x_1494_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1493_);
lean_del_object(v___x_1485_);
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1555_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_val_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1555_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_nat_abs(v_mantissa_1469_);
lean_dec(v_mantissa_1469_);
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1492_, v_a_1499_);
if (lean_obj_tag(v___x_1500_) == 1)
{
lean_object* v_val_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_a_1499_);
lean_del_object(v___x_1489_);
v_val_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1545_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_val_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1545_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_nat_abs(v_mantissa_1477_);
lean_dec(v_mantissa_1477_);
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1492_, v_a_1505_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1508_; 
lean_dec(v_a_1505_);
lean_del_object(v___x_1503_);
lean_del_object(v___x_1497_);
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1487_, v_a_1440_);
lean_dec_ref(v_s_1487_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1527_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1527_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1527_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_fst_1513_; lean_object* v_snd_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1526_; 
v_fst_1513_ = lean_ctor_get(v_a_1509_, 0);
v_snd_1514_ = lean_ctor_get(v_a_1509_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_a_1509_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1516_ = v_a_1509_;
v_isShared_1517_ = v_isSharedCheck_1526_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_snd_1514_);
lean_inc(v_fst_1513_);
lean_dec(v_a_1509_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1526_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = lean_unbox(v_fst_1513_);
lean_dec(v_fst_1513_);
v___x_1519_ = l_Lean_Expr_lam___override(v_val_1495_, v_val_1501_, v_val_1507_, v___x_1518_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1519_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_snd_1514_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1521_);
v___x_1523_ = v___x_1511_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_val_1507_);
lean_dec(v_val_1501_);
lean_dec(v_val_1495_);
v_a_1528_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1508_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1508_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec(v___x_1506_);
lean_dec(v_val_1501_);
lean_dec(v_val_1495_);
lean_dec_ref(v_s_1487_);
lean_dec_ref(v_a_1440_);
v___x_1536_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1537_ = l_Nat_reprFast(v_a_1505_);
v___x_1538_ = lean_string_append(v___x_1536_, v___x_1537_);
lean_dec_ref(v___x_1537_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 18);
lean_ctor_set(v___x_1503_, 0, v___x_1538_);
v___x_1540_ = v___x_1503_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1540_);
v___x_1542_ = v___x_1497_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_dec(v___x_1500_);
lean_dec(v_val_1495_);
lean_dec_ref(v_s_1487_);
lean_dec(v_mantissa_1477_);
lean_dec_ref(v_a_1440_);
v___x_1546_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1547_ = l_Nat_reprFast(v_a_1499_);
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 18);
lean_ctor_set(v___x_1497_, 0, v___x_1548_);
v___x_1550_ = v___x_1497_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 1);
lean_ctor_set(v___x_1489_, 0, v___x_1550_);
v___x_1552_ = v___x_1489_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
lean_dec(v___x_1494_);
lean_dec_ref(v_s_1487_);
lean_dec(v_mantissa_1477_);
lean_dec(v_mantissa_1469_);
lean_dec_ref(v_a_1440_);
v___x_1556_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1557_ = l_Nat_reprFast(v_a_1493_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
lean_dec_ref(v___x_1557_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 18);
lean_ctor_set(v___x_1489_, 0, v___x_1558_);
v___x_1560_ = v___x_1489_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1560_);
v___x_1562_ = v___x_1485_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_1485_);
lean_dec(v_val_1483_);
lean_dec(v_mantissa_1477_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1451_;
}
}
}
else
{
lean_dec(v___x_1482_);
lean_dec(v_mantissa_1477_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1451_;
}
}
}
else
{
lean_dec(v_exponent_1478_);
lean_dec(v_mantissa_1477_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1448_;
}
}
else
{
lean_dec(v_val_1475_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1448_;
}
}
else
{
lean_dec(v___x_1474_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1448_;
}
}
}
else
{
lean_dec(v_exponent_1470_);
lean_dec(v_mantissa_1469_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1445_;
}
}
else
{
lean_dec(v_val_1467_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1445_;
}
}
else
{
lean_dec(v___x_1466_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1445_;
}
}
}
else
{
lean_dec(v_exponent_1460_);
lean_dec(v_mantissa_1459_);
lean_dec_ref(v_a_1440_);
goto v___jp_1442_;
}
}
else
{
lean_dec(v_val_1457_);
lean_dec_ref(v_a_1440_);
goto v___jp_1442_;
}
}
else
{
lean_dec(v___x_1456_);
lean_dec_ref(v_a_1440_);
goto v___jp_1442_;
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v_a_1440_);
v___x_1567_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
v___jp_1442_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
v___jp_1445_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
v___jp_1448_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
v___jp_1451_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1439_ = stack[0].m_obj;
lean_object* v_a_1440_ = stack[1].m_obj;
lean_object* v_res_1569_;
v_res_1569_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_json_1439_, v_a_1440_);
stack->m_obj
 = v_res_1569_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___boxed(lean_object* v_json_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_json_1570_, v_a_1571_);
lean_dec(v_json_1570_);
return v_res_1573_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(lean_object* v_json_1577_, lean_object* v_a_1578_){
_start:
{
if (lean_obj_tag(v_json_1577_) == 5)
{
lean_object* v_kvPairs_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_kvPairs_1592_ = lean_ctor_get(v_json_1577_, 0);
v___x_1593_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1592_, v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 1)
{
lean_object* v_val_1595_; 
v_val_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v___x_1594_, 1);
if (lean_obj_tag(v_val_1595_) == 2)
{
lean_object* v_n_1596_; lean_object* v_mantissa_1597_; lean_object* v_exponent_1598_; lean_object* v_natZero_1599_; lean_object* v_intZero_1600_; uint8_t v_isNeg_1601_; 
v_n_1596_ = lean_ctor_get(v_val_1595_, 0);
lean_inc_ref(v_n_1596_);
lean_dec_ref_known(v_val_1595_, 1);
v_mantissa_1597_ = lean_ctor_get(v_n_1596_, 0);
lean_inc(v_mantissa_1597_);
v_exponent_1598_ = lean_ctor_get(v_n_1596_, 1);
lean_inc(v_exponent_1598_);
lean_dec_ref(v_n_1596_);
v_natZero_1599_ = lean_unsigned_to_nat(0u);
v_intZero_1600_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1601_ = lean_int_dec_lt(v_mantissa_1597_, v_intZero_1600_);
if (v_isNeg_1601_ == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_eq(v_exponent_1598_, v_natZero_1599_);
lean_dec(v_exponent_1598_);
if (v___x_1602_ == 0)
{
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1592_, v___x_1603_);
if (lean_obj_tag(v___x_1604_) == 1)
{
lean_object* v_val_1605_; 
v_val_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v___x_1604_, 1);
if (lean_obj_tag(v_val_1605_) == 2)
{
lean_object* v_n_1606_; lean_object* v_mantissa_1607_; lean_object* v_exponent_1608_; uint8_t v_isNeg_1609_; 
v_n_1606_ = lean_ctor_get(v_val_1605_, 0);
lean_inc_ref(v_n_1606_);
lean_dec_ref_known(v_val_1605_, 1);
v_mantissa_1607_ = lean_ctor_get(v_n_1606_, 0);
lean_inc(v_mantissa_1607_);
v_exponent_1608_ = lean_ctor_get(v_n_1606_, 1);
lean_inc(v_exponent_1608_);
lean_dec_ref(v_n_1606_);
v_isNeg_1609_ = lean_int_dec_lt(v_mantissa_1607_, v_intZero_1600_);
if (v_isNeg_1609_ == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_eq(v_exponent_1608_, v_natZero_1599_);
lean_dec(v_exponent_1608_);
if (v___x_1610_ == 0)
{
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1583_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1612_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1592_, v___x_1611_);
if (lean_obj_tag(v___x_1612_) == 1)
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___x_1612_, 1);
if (lean_obj_tag(v_val_1613_) == 2)
{
lean_object* v_n_1614_; lean_object* v_mantissa_1615_; lean_object* v_exponent_1616_; uint8_t v_isNeg_1617_; 
v_n_1614_ = lean_ctor_get(v_val_1613_, 0);
lean_inc_ref(v_n_1614_);
lean_dec_ref_known(v_val_1613_, 1);
v_mantissa_1615_ = lean_ctor_get(v_n_1614_, 0);
lean_inc(v_mantissa_1615_);
v_exponent_1616_ = lean_ctor_get(v_n_1614_, 1);
lean_inc(v_exponent_1616_);
lean_dec_ref(v_n_1614_);
v_isNeg_1617_ = lean_int_dec_lt(v_mantissa_1615_, v_intZero_1600_);
if (v_isNeg_1617_ == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_nat_dec_eq(v_exponent_1616_, v_natZero_1599_);
lean_dec(v_exponent_1616_);
if (v___x_1618_ == 0)
{
lean_dec(v_mantissa_1615_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1586_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1592_, v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 1)
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1704_; 
v_val_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1704_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1704_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
if (lean_obj_tag(v_val_1621_) == 3)
{
lean_object* v_s_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1703_; 
v_s_1625_ = lean_ctor_get(v_val_1621_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_val_1621_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1627_ = v_val_1621_;
v_isShared_1628_ = v_isSharedCheck_1703_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_s_1625_);
lean_dec(v_val_1621_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1703_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_nameMap_1629_; lean_object* v_exprMap_1630_; lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_nameMap_1629_ = lean_ctor_get(v_a_1578_, 1);
v_exprMap_1630_ = lean_ctor_get(v_a_1578_, 3);
v_a_1631_ = lean_nat_abs(v_mantissa_1597_);
lean_dec(v_mantissa_1597_);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1629_, v_a_1631_);
if (lean_obj_tag(v___x_1632_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1631_);
lean_del_object(v___x_1623_);
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1693_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_val_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1693_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_nat_abs(v_mantissa_1607_);
lean_dec(v_mantissa_1607_);
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1630_, v_a_1637_);
if (lean_obj_tag(v___x_1638_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_a_1637_);
lean_del_object(v___x_1627_);
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1683_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1683_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_nat_abs(v_mantissa_1615_);
lean_dec(v_mantissa_1615_);
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1630_, v_a_1643_);
if (lean_obj_tag(v___x_1644_) == 1)
{
lean_object* v_val_1645_; lean_object* v___x_1646_; 
lean_dec(v_a_1643_);
lean_del_object(v___x_1641_);
lean_del_object(v___x_1635_);
v_val_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1625_, v_a_1578_);
lean_dec_ref(v_s_1625_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1665_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1665_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1665_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; lean_object* v_snd_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1664_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
v_snd_1652_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1654_ = v_a_1647_;
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snd_1652_);
lean_inc(v_fst_1651_);
lean_dec(v_a_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1656_ = lean_unbox(v_fst_1651_);
lean_dec(v_fst_1651_);
v___x_1657_ = l_Lean_Expr_forallE___override(v_val_1633_, v_val_1639_, v_val_1645_, v___x_1656_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_snd_1652_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1659_);
v___x_1661_ = v___x_1649_;
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
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_val_1645_);
lean_dec(v_val_1639_);
lean_dec(v_val_1633_);
v_a_1666_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1646_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1646_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
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
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_dec(v___x_1644_);
lean_dec(v_val_1639_);
lean_dec(v_val_1633_);
lean_dec_ref(v_s_1625_);
lean_dec_ref(v_a_1578_);
v___x_1674_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1675_ = l_Nat_reprFast(v_a_1643_);
v___x_1676_ = lean_string_append(v___x_1674_, v___x_1675_);
lean_dec_ref(v___x_1675_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 18);
lean_ctor_set(v___x_1641_, 0, v___x_1676_);
v___x_1678_ = v___x_1641_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1678_);
v___x_1680_ = v___x_1635_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_dec(v___x_1638_);
lean_dec(v_val_1633_);
lean_dec_ref(v_s_1625_);
lean_dec(v_mantissa_1615_);
lean_dec_ref(v_a_1578_);
v___x_1684_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1685_ = l_Nat_reprFast(v_a_1637_);
v___x_1686_ = lean_string_append(v___x_1684_, v___x_1685_);
lean_dec_ref(v___x_1685_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 18);
lean_ctor_set(v___x_1635_, 0, v___x_1686_);
v___x_1688_ = v___x_1635_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 1);
lean_ctor_set(v___x_1627_, 0, v___x_1688_);
v___x_1690_ = v___x_1627_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v___x_1632_);
lean_dec_ref(v_s_1625_);
lean_dec(v_mantissa_1615_);
lean_dec(v_mantissa_1607_);
lean_dec_ref(v_a_1578_);
v___x_1694_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1695_ = l_Nat_reprFast(v_a_1631_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 18);
lean_ctor_set(v___x_1627_, 0, v___x_1696_);
v___x_1698_ = v___x_1627_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1698_);
v___x_1700_ = v___x_1623_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_del_object(v___x_1623_);
lean_dec(v_val_1621_);
lean_dec(v_mantissa_1615_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1589_;
}
}
}
else
{
lean_dec(v___x_1620_);
lean_dec(v_mantissa_1615_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1589_;
}
}
}
else
{
lean_dec(v_exponent_1616_);
lean_dec(v_mantissa_1615_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1586_;
}
}
else
{
lean_dec(v_val_1613_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1586_;
}
}
else
{
lean_dec(v___x_1612_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1586_;
}
}
}
else
{
lean_dec(v_exponent_1608_);
lean_dec(v_mantissa_1607_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1583_;
}
}
else
{
lean_dec(v_val_1605_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1583_;
}
}
else
{
lean_dec(v___x_1604_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1583_;
}
}
}
else
{
lean_dec(v_exponent_1598_);
lean_dec(v_mantissa_1597_);
lean_dec_ref(v_a_1578_);
goto v___jp_1580_;
}
}
else
{
lean_dec(v_val_1595_);
lean_dec_ref(v_a_1578_);
goto v___jp_1580_;
}
}
else
{
lean_dec(v___x_1594_);
lean_dec_ref(v_a_1578_);
goto v___jp_1580_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v_a_1578_);
v___x_1705_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
v___jp_1580_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
v___jp_1583_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
v___jp_1586_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
v___jp_1589_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_res_1707_;
v_res_1707_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_json_1577_, v_a_1578_);
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___boxed(lean_object* v_json_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_json_1708_, v_a_1709_);
lean_dec(v_json_1708_);
return v_res_1711_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(lean_object* v_json_1717_, lean_object* v_a_1718_){
_start:
{
if (lean_obj_tag(v_json_1717_) == 5)
{
lean_object* v_kvPairs_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_kvPairs_1735_ = lean_ctor_get(v_json_1717_, 0);
v___x_1736_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1735_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 1)
{
lean_object* v_val_1738_; 
v_val_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v___x_1737_, 1);
if (lean_obj_tag(v_val_1738_) == 2)
{
lean_object* v_n_1739_; lean_object* v_mantissa_1740_; lean_object* v_exponent_1741_; lean_object* v_natZero_1742_; lean_object* v_intZero_1743_; uint8_t v_isNeg_1744_; 
v_n_1739_ = lean_ctor_get(v_val_1738_, 0);
lean_inc_ref(v_n_1739_);
lean_dec_ref_known(v_val_1738_, 1);
v_mantissa_1740_ = lean_ctor_get(v_n_1739_, 0);
lean_inc(v_mantissa_1740_);
v_exponent_1741_ = lean_ctor_get(v_n_1739_, 1);
lean_inc(v_exponent_1741_);
lean_dec_ref(v_n_1739_);
v_natZero_1742_ = lean_unsigned_to_nat(0u);
v_intZero_1743_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1744_ = lean_int_dec_lt(v_mantissa_1740_, v_intZero_1743_);
if (v_isNeg_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_eq(v_exponent_1741_, v_natZero_1742_);
lean_dec(v_exponent_1741_);
if (v___x_1745_ == 0)
{
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1720_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1735_, v___x_1746_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; 
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1747_, 1);
if (lean_obj_tag(v_val_1748_) == 2)
{
lean_object* v_n_1749_; lean_object* v_mantissa_1750_; lean_object* v_exponent_1751_; uint8_t v_isNeg_1752_; 
v_n_1749_ = lean_ctor_get(v_val_1748_, 0);
lean_inc_ref(v_n_1749_);
lean_dec_ref_known(v_val_1748_, 1);
v_mantissa_1750_ = lean_ctor_get(v_n_1749_, 0);
lean_inc(v_mantissa_1750_);
v_exponent_1751_ = lean_ctor_get(v_n_1749_, 1);
lean_inc(v_exponent_1751_);
lean_dec_ref(v_n_1749_);
v_isNeg_1752_ = lean_int_dec_lt(v_mantissa_1750_, v_intZero_1743_);
if (v_isNeg_1752_ == 0)
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_eq(v_exponent_1751_, v_natZero_1742_);
lean_dec(v_exponent_1751_);
if (v___x_1753_ == 0)
{
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1723_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1735_, v___x_1754_);
if (lean_obj_tag(v___x_1755_) == 1)
{
lean_object* v_val_1756_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1755_, 1);
if (lean_obj_tag(v_val_1756_) == 2)
{
lean_object* v_n_1757_; lean_object* v_mantissa_1758_; lean_object* v_exponent_1759_; uint8_t v_isNeg_1760_; 
v_n_1757_ = lean_ctor_get(v_val_1756_, 0);
lean_inc_ref(v_n_1757_);
lean_dec_ref_known(v_val_1756_, 1);
v_mantissa_1758_ = lean_ctor_get(v_n_1757_, 0);
lean_inc(v_mantissa_1758_);
v_exponent_1759_ = lean_ctor_get(v_n_1757_, 1);
lean_inc(v_exponent_1759_);
lean_dec_ref(v_n_1757_);
v_isNeg_1760_ = lean_int_dec_lt(v_mantissa_1758_, v_intZero_1743_);
if (v_isNeg_1760_ == 0)
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_eq(v_exponent_1759_, v_natZero_1742_);
lean_dec(v_exponent_1759_);
if (v___x_1761_ == 0)
{
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1726_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1763_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1735_, v___x_1762_);
if (lean_obj_tag(v___x_1763_) == 1)
{
lean_object* v_val_1764_; 
v_val_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_val_1764_) == 2)
{
lean_object* v_n_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1858_; 
v_n_1765_ = lean_ctor_get(v_val_1764_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_val_1764_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1767_ = v_val_1764_;
v_isShared_1768_ = v_isSharedCheck_1858_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_n_1765_);
lean_dec(v_val_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1858_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_mantissa_1769_; lean_object* v_exponent_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1857_; 
v_mantissa_1769_ = lean_ctor_get(v_n_1765_, 0);
v_exponent_1770_ = lean_ctor_get(v_n_1765_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_n_1765_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1772_ = v_n_1765_;
v_isShared_1773_ = v_isSharedCheck_1857_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_exponent_1770_);
lean_inc(v_mantissa_1769_);
lean_dec(v_n_1765_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1857_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v_isNeg_1774_; 
v_isNeg_1774_ = lean_int_dec_lt(v_mantissa_1769_, v_intZero_1743_);
if (v_isNeg_1774_ == 0)
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_eq(v_exponent_1770_, v_natZero_1742_);
lean_dec(v_exponent_1770_);
if (v___x_1775_ == 0)
{
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_del_object(v___x_1767_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3));
v___x_1777_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1735_, v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1856_; 
v_val_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1856_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1856_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
if (lean_obj_tag(v_val_1778_) == 1)
{
uint8_t v_b_1782_; lean_object* v_nameMap_1783_; lean_object* v_exprMap_1784_; lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_b_1782_ = lean_ctor_get_uint8(v_val_1778_, 0);
lean_dec_ref_known(v_val_1778_, 0);
v_nameMap_1783_ = lean_ctor_get(v_a_1718_, 1);
v_exprMap_1784_ = lean_ctor_get(v_a_1718_, 3);
v_a_1785_ = lean_nat_abs(v_mantissa_1740_);
lean_dec(v_mantissa_1740_);
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1783_, v_a_1785_);
if (lean_obj_tag(v___x_1786_) == 1)
{
lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1785_);
lean_del_object(v___x_1767_);
v_val_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1846_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1846_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_nat_abs(v_mantissa_1750_);
lean_dec(v_mantissa_1750_);
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1784_, v_a_1791_);
if (lean_obj_tag(v___x_1792_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_a_1791_);
lean_del_object(v___x_1780_);
v_val_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1836_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_val_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1836_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_nat_abs(v_mantissa_1758_);
lean_dec(v_mantissa_1758_);
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1784_, v_a_1797_);
if (lean_obj_tag(v___x_1798_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1797_);
lean_del_object(v___x_1789_);
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1826_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_val_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1826_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_a_1803_; lean_object* v___x_1804_; 
v_a_1803_ = lean_nat_abs(v_mantissa_1769_);
lean_dec(v_mantissa_1769_);
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1784_, v_a_1803_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1803_);
lean_del_object(v___x_1801_);
lean_del_object(v___x_1795_);
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1816_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_val_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1816_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_Expr_letE___override(v_val_1787_, v_val_1793_, v_val_1799_, v_val_1805_, v_b_1782_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_a_1718_);
lean_ctor_set(v___x_1772_, 0, v___x_1809_);
v___x_1811_ = v___x_1772_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1718_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1811_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec(v___x_1804_);
lean_dec(v_val_1799_);
lean_dec(v_val_1793_);
lean_dec(v_val_1787_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_a_1718_);
v___x_1817_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1818_ = l_Nat_reprFast(v_a_1803_);
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
lean_dec_ref(v___x_1818_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 18);
lean_ctor_set(v___x_1801_, 0, v___x_1819_);
v___x_1821_ = v___x_1801_;
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
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1821_);
v___x_1823_ = v___x_1795_;
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
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec(v___x_1798_);
lean_dec(v_val_1793_);
lean_dec(v_val_1787_);
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_dec_ref(v_a_1718_);
v___x_1827_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1828_ = l_Nat_reprFast(v_a_1797_);
v___x_1829_ = lean_string_append(v___x_1827_, v___x_1828_);
lean_dec_ref(v___x_1828_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 18);
lean_ctor_set(v___x_1795_, 0, v___x_1829_);
v___x_1831_ = v___x_1795_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1831_);
v___x_1833_ = v___x_1789_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v___x_1792_);
lean_dec(v_val_1787_);
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_dec(v_mantissa_1758_);
lean_dec_ref(v_a_1718_);
v___x_1837_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1838_ = l_Nat_reprFast(v_a_1791_);
v___x_1839_ = lean_string_append(v___x_1837_, v___x_1838_);
lean_dec_ref(v___x_1838_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 18);
lean_ctor_set(v___x_1789_, 0, v___x_1839_);
v___x_1841_ = v___x_1789_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1841_);
v___x_1843_ = v___x_1780_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v___x_1786_);
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec_ref(v_a_1718_);
v___x_1847_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1848_ = l_Nat_reprFast(v_a_1785_);
v___x_1849_ = lean_string_append(v___x_1847_, v___x_1848_);
lean_dec_ref(v___x_1848_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 18);
lean_ctor_set(v___x_1780_, 0, v___x_1849_);
v___x_1851_ = v___x_1780_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 1);
lean_ctor_set(v___x_1767_, 0, v___x_1851_);
v___x_1853_ = v___x_1767_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_del_object(v___x_1780_);
lean_dec(v_val_1778_);
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_del_object(v___x_1767_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1732_;
}
}
}
else
{
lean_dec(v___x_1777_);
lean_del_object(v___x_1772_);
lean_dec(v_mantissa_1769_);
lean_del_object(v___x_1767_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1732_;
}
}
}
else
{
lean_del_object(v___x_1772_);
lean_dec(v_exponent_1770_);
lean_dec(v_mantissa_1769_);
lean_del_object(v___x_1767_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1729_;
}
}
}
}
else
{
lean_dec(v_val_1764_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1729_;
}
}
else
{
lean_dec(v___x_1763_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1729_;
}
}
}
else
{
lean_dec(v_exponent_1759_);
lean_dec(v_mantissa_1758_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1726_;
}
}
else
{
lean_dec(v_val_1756_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1726_;
}
}
else
{
lean_dec(v___x_1755_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1726_;
}
}
}
else
{
lean_dec(v_exponent_1751_);
lean_dec(v_mantissa_1750_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1723_;
}
}
else
{
lean_dec(v_val_1748_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1723_;
}
}
else
{
lean_dec(v___x_1747_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1723_;
}
}
}
else
{
lean_dec(v_exponent_1741_);
lean_dec(v_mantissa_1740_);
lean_dec_ref(v_a_1718_);
goto v___jp_1720_;
}
}
else
{
lean_dec(v_val_1738_);
lean_dec_ref(v_a_1718_);
goto v___jp_1720_;
}
}
else
{
lean_dec(v___x_1737_);
lean_dec_ref(v_a_1718_);
goto v___jp_1720_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v_a_1718_);
v___x_1859_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
v___jp_1720_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
v___jp_1723_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
v___jp_1726_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
v___jp_1732_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1717_ = stack[0].m_obj;
lean_object* v_a_1718_ = stack[1].m_obj;
lean_object* v_res_1861_;
v_res_1861_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_json_1717_, v_a_1718_);
stack->m_obj
 = v_res_1861_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___boxed(lean_object* v_json_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_json_1862_, v_a_1863_);
lean_dec(v_json_1862_);
return v_res_1865_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(lean_object* v_json_1872_, lean_object* v_a_1873_){
_start:
{
if (lean_obj_tag(v_json_1872_) == 5)
{
lean_object* v_kvPairs_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_kvPairs_1884_ = lean_ctor_get(v_json_1872_, 0);
v___x_1885_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2));
v___x_1886_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1884_, v___x_1885_);
if (lean_obj_tag(v___x_1886_) == 1)
{
lean_object* v_val_1887_; 
v_val_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v___x_1886_, 1);
if (lean_obj_tag(v_val_1887_) == 2)
{
lean_object* v_n_1888_; lean_object* v_mantissa_1889_; lean_object* v_exponent_1890_; lean_object* v_natZero_1891_; lean_object* v_intZero_1892_; uint8_t v_isNeg_1893_; 
v_n_1888_ = lean_ctor_get(v_val_1887_, 0);
lean_inc_ref(v_n_1888_);
lean_dec_ref_known(v_val_1887_, 1);
v_mantissa_1889_ = lean_ctor_get(v_n_1888_, 0);
lean_inc(v_mantissa_1889_);
v_exponent_1890_ = lean_ctor_get(v_n_1888_, 1);
lean_inc(v_exponent_1890_);
lean_dec_ref(v_n_1888_);
v_natZero_1891_ = lean_unsigned_to_nat(0u);
v_intZero_1892_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1893_ = lean_int_dec_lt(v_mantissa_1889_, v_intZero_1892_);
if (v_isNeg_1893_ == 0)
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_eq(v_exponent_1890_, v_natZero_1891_);
lean_dec(v_exponent_1890_);
if (v___x_1894_ == 0)
{
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1875_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3));
v___x_1896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1884_, v___x_1895_);
if (lean_obj_tag(v___x_1896_) == 1)
{
lean_object* v_val_1897_; 
v_val_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v___x_1896_, 1);
if (lean_obj_tag(v_val_1897_) == 2)
{
lean_object* v_n_1898_; lean_object* v_mantissa_1899_; lean_object* v_exponent_1900_; uint8_t v_isNeg_1901_; 
v_n_1898_ = lean_ctor_get(v_val_1897_, 0);
lean_inc_ref(v_n_1898_);
lean_dec_ref_known(v_val_1897_, 1);
v_mantissa_1899_ = lean_ctor_get(v_n_1898_, 0);
lean_inc(v_mantissa_1899_);
v_exponent_1900_ = lean_ctor_get(v_n_1898_, 1);
lean_inc(v_exponent_1900_);
lean_dec_ref(v_n_1898_);
v_isNeg_1901_ = lean_int_dec_lt(v_mantissa_1899_, v_intZero_1892_);
if (v_isNeg_1901_ == 0)
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_nat_dec_eq(v_exponent_1900_, v_natZero_1891_);
lean_dec(v_exponent_1900_);
if (v___x_1902_ == 0)
{
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4));
v___x_1904_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1884_, v___x_1903_);
if (lean_obj_tag(v___x_1904_) == 1)
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1964_; 
v_val_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1964_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1964_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
if (lean_obj_tag(v_val_1905_) == 2)
{
lean_object* v_n_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1963_; 
v_n_1909_ = lean_ctor_get(v_val_1905_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_val_1905_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1911_ = v_val_1905_;
v_isShared_1912_ = v_isSharedCheck_1963_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_n_1909_);
lean_dec(v_val_1905_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1963_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_mantissa_1913_; lean_object* v_exponent_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1962_; 
v_mantissa_1913_ = lean_ctor_get(v_n_1909_, 0);
v_exponent_1914_ = lean_ctor_get(v_n_1909_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_n_1909_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1916_ = v_n_1909_;
v_isShared_1917_ = v_isSharedCheck_1962_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_exponent_1914_);
lean_inc(v_mantissa_1913_);
lean_dec(v_n_1909_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1962_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
uint8_t v_isNeg_1918_; 
v_isNeg_1918_ = lean_int_dec_lt(v_mantissa_1913_, v_intZero_1892_);
if (v_isNeg_1918_ == 0)
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_eq(v_exponent_1914_, v_natZero_1891_);
lean_dec(v_exponent_1914_);
if (v___x_1919_ == 0)
{
lean_del_object(v___x_1916_);
lean_dec(v_mantissa_1913_);
lean_del_object(v___x_1911_);
lean_del_object(v___x_1907_);
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1881_;
}
else
{
lean_object* v_nameMap_1920_; lean_object* v_exprMap_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_nameMap_1920_ = lean_ctor_get(v_a_1873_, 1);
v_exprMap_1921_ = lean_ctor_get(v_a_1873_, 3);
v_a_1922_ = lean_nat_abs(v_mantissa_1889_);
lean_dec(v_mantissa_1889_);
v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1920_, v_a_1922_);
if (lean_obj_tag(v___x_1923_) == 1)
{
lean_object* v_val_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1922_);
lean_del_object(v___x_1907_);
v_val_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1952_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_val_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1952_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_nat_abs(v_mantissa_1913_);
lean_dec(v_mantissa_1913_);
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1921_, v_a_1928_);
if (lean_obj_tag(v___x_1929_) == 1)
{
lean_object* v_val_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1928_);
lean_del_object(v___x_1926_);
lean_del_object(v___x_1911_);
v_val_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_val_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v_a_1934_ = lean_nat_abs(v_mantissa_1899_);
lean_dec(v_mantissa_1899_);
v___x_1935_ = l_Lean_Expr_proj___override(v_val_1924_, v_a_1934_, v_val_1930_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_a_1873_);
lean_ctor_set(v___x_1916_, 0, v___x_1935_);
v___x_1937_ = v___x_1916_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_a_1873_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1937_);
v___x_1939_ = v___x_1932_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec(v___x_1929_);
lean_dec(v_val_1924_);
lean_del_object(v___x_1916_);
lean_dec(v_mantissa_1899_);
lean_dec_ref(v_a_1873_);
v___x_1943_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1944_ = l_Nat_reprFast(v_a_1928_);
v___x_1945_ = lean_string_append(v___x_1943_, v___x_1944_);
lean_dec_ref(v___x_1944_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 18);
lean_ctor_set(v___x_1926_, 0, v___x_1945_);
v___x_1947_ = v___x_1926_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
lean_ctor_set(v___x_1911_, 0, v___x_1947_);
v___x_1949_ = v___x_1911_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec(v___x_1923_);
lean_del_object(v___x_1916_);
lean_dec(v_mantissa_1913_);
lean_dec(v_mantissa_1899_);
lean_dec_ref(v_a_1873_);
v___x_1953_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1954_ = l_Nat_reprFast(v_a_1922_);
v___x_1955_ = lean_string_append(v___x_1953_, v___x_1954_);
lean_dec_ref(v___x_1954_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 18);
lean_ctor_set(v___x_1911_, 0, v___x_1955_);
v___x_1957_ = v___x_1911_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1957_);
v___x_1959_ = v___x_1907_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
lean_del_object(v___x_1916_);
lean_dec(v_exponent_1914_);
lean_dec(v_mantissa_1913_);
lean_del_object(v___x_1911_);
lean_del_object(v___x_1907_);
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1881_;
}
}
}
}
else
{
lean_del_object(v___x_1907_);
lean_dec(v_val_1905_);
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1881_;
}
}
}
else
{
lean_dec(v___x_1904_);
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1881_;
}
}
}
else
{
lean_dec(v_exponent_1900_);
lean_dec(v_mantissa_1899_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1878_;
}
}
else
{
lean_dec(v_val_1897_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1878_;
}
}
else
{
lean_dec(v___x_1896_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1878_;
}
}
}
else
{
lean_dec(v_exponent_1890_);
lean_dec(v_mantissa_1889_);
lean_dec_ref(v_a_1873_);
goto v___jp_1875_;
}
}
else
{
lean_dec(v_val_1887_);
lean_dec_ref(v_a_1873_);
goto v___jp_1875_;
}
}
else
{
lean_dec(v___x_1886_);
lean_dec_ref(v_a_1873_);
goto v___jp_1875_;
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_a_1873_);
v___x_1965_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
v___jp_1875_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
v___jp_1878_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
v___jp_1881_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1872_ = stack[0].m_obj;
lean_object* v_a_1873_ = stack[1].m_obj;
lean_object* v_res_1967_;
v_res_1967_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_json_1872_, v_a_1873_);
stack->m_obj
 = v_res_1967_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___boxed(lean_object* v_json_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_json_1968_, v_a_1969_);
lean_dec(v_json_1968_);
return v_res_1971_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(lean_object* v_json_1975_, lean_object* v_a_1976_){
_start:
{
if (lean_obj_tag(v_json_1975_) == 3)
{
lean_object* v_s_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2003_; 
v_s_1978_ = lean_ctor_get(v_json_1975_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_json_1975_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1980_ = v_json_1975_;
v_isShared_1981_ = v_isSharedCheck_2003_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_s_1978_);
lean_dec(v_json_1975_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2003_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_string_utf8_byte_size(v_s_1978_);
v___x_1984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1984_, 0, v_s_1978_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1983_);
v___x_1985_ = l_String_Slice_toNat_x3f(v___x_1984_);
lean_dec_ref_known(v___x_1984_, 3);
if (lean_obj_tag(v___x_1985_) == 1)
{
lean_object* v_val_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
v_val_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_val_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 0);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_val_1986_);
v___x_1991_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = l_Lean_Expr_lit___override(v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v_a_1976_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 0);
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
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec(v___x_1985_);
lean_dec_ref(v_a_1976_);
v___x_1999_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 0, v___x_1999_);
v___x_2001_ = v___x_1980_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
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
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec_ref(v_a_1976_);
lean_dec(v_json_1975_);
v___x_2004_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_1975_ = stack[0].m_obj;
lean_object* v_a_1976_ = stack[1].m_obj;
lean_object* v_res_2006_;
v_res_2006_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_json_1975_, v_a_1976_);
stack->m_obj
 = v_res_2006_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___boxed(lean_object* v_json_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_json_2007_, v_a_2008_);
return v_res_2010_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(lean_object* v_json_2014_, lean_object* v_a_2015_){
_start:
{
if (lean_obj_tag(v_json_2014_) == 3)
{
lean_object* v_s_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_s_2017_ = lean_ctor_get(v_json_2014_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_json_2014_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2019_ = v_json_2014_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_s_2017_);
lean_dec(v_json_2014_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 1);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_s_2017_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = l_Lean_Expr_lit___override(v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v_a_2015_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v_a_2015_);
lean_dec(v_json_2014_);
v___x_2028_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1));
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_2014_ = stack[0].m_obj;
lean_object* v_a_2015_ = stack[1].m_obj;
lean_object* v_res_2030_;
v_res_2030_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_json_2014_, v_a_2015_);
stack->m_obj
 = v_res_2030_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___boxed(lean_object* v_json_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_json_2031_, v_a_2032_);
return v_res_2034_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(lean_object* v_json_2040_, lean_object* v_a_2041_){
_start:
{
if (lean_obj_tag(v_json_2040_) == 5)
{
lean_object* v_kvPairs_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_kvPairs_2049_ = lean_ctor_get(v_json_2040_, 0);
v___x_2050_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2));
v___x_2051_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2049_, v___x_2050_);
if (lean_obj_tag(v___x_2051_) == 1)
{
lean_object* v_val_2052_; 
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v___x_2051_, 1);
if (lean_obj_tag(v_val_2052_) == 2)
{
lean_object* v_n_2053_; lean_object* v_mantissa_2054_; lean_object* v_exponent_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2100_; 
v_n_2053_ = lean_ctor_get(v_val_2052_, 0);
lean_inc_ref(v_n_2053_);
lean_dec_ref_known(v_val_2052_, 1);
v_mantissa_2054_ = lean_ctor_get(v_n_2053_, 0);
v_exponent_2055_ = lean_ctor_get(v_n_2053_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_n_2053_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2057_ = v_n_2053_;
v_isShared_2058_ = v_isSharedCheck_2100_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_exponent_2055_);
lean_inc(v_mantissa_2054_);
lean_dec(v_n_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2100_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_natZero_2059_; lean_object* v_intZero_2060_; uint8_t v_isNeg_2061_; 
v_natZero_2059_ = lean_unsigned_to_nat(0u);
v_intZero_2060_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2061_ = lean_int_dec_lt(v_mantissa_2054_, v_intZero_2060_);
if (v_isNeg_2061_ == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_nat_dec_eq(v_exponent_2055_, v_natZero_2059_);
lean_dec(v_exponent_2055_);
if (v___x_2062_ == 0)
{
lean_del_object(v___x_2057_);
lean_dec(v_mantissa_2054_);
lean_dec_ref(v_a_2041_);
goto v___jp_2043_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3));
v___x_2064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2049_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2099_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2099_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_val_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2099_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
if (lean_obj_tag(v_val_2065_) == 5)
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2097_; 
v_isSharedCheck_2097_ = !lean_is_exclusive(v_val_2065_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_val_2065_, 0);
lean_dec(v_unused_2098_);
v___x_2070_ = v_val_2065_;
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_val_2065_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_exprMap_2072_; lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_exprMap_2072_ = lean_ctor_get(v_a_2041_, 3);
v_a_2073_ = lean_nat_abs(v_mantissa_2054_);
lean_dec(v_mantissa_2054_);
v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_a_2073_);
lean_del_object(v___x_2070_);
lean_del_object(v___x_2067_);
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_val_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = l_Lean_Expr_mdata___override(v___x_2079_, v_val_2075_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_a_2041_);
lean_ctor_set(v___x_2057_, 0, v___x_2080_);
v___x_2082_ = v___x_2057_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_a_2041_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2082_);
v___x_2084_ = v___x_2077_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v___x_2074_);
lean_del_object(v___x_2057_);
lean_dec_ref(v_a_2041_);
v___x_2088_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2089_ = l_Nat_reprFast(v_a_2073_);
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
lean_dec_ref(v___x_2089_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 18);
lean_ctor_set(v___x_2070_, 0, v___x_2090_);
v___x_2092_ = v___x_2070_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2092_);
v___x_2094_ = v___x_2067_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_del_object(v___x_2067_);
lean_dec(v_val_2065_);
lean_del_object(v___x_2057_);
lean_dec(v_mantissa_2054_);
lean_dec_ref(v_a_2041_);
goto v___jp_2046_;
}
}
}
else
{
lean_dec(v___x_2064_);
lean_del_object(v___x_2057_);
lean_dec(v_mantissa_2054_);
lean_dec_ref(v_a_2041_);
goto v___jp_2046_;
}
}
}
else
{
lean_del_object(v___x_2057_);
lean_dec(v_exponent_2055_);
lean_dec(v_mantissa_2054_);
lean_dec_ref(v_a_2041_);
goto v___jp_2043_;
}
}
}
else
{
lean_dec(v_val_2052_);
lean_dec_ref(v_a_2041_);
goto v___jp_2043_;
}
}
else
{
lean_dec(v___x_2051_);
lean_dec_ref(v_a_2041_);
goto v___jp_2043_;
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v_a_2041_);
v___x_2101_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
v___jp_2043_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
v___jp_2046_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_2040_ = stack[0].m_obj;
lean_object* v_a_2041_ = stack[1].m_obj;
lean_object* v_res_2103_;
v_res_2103_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_json_2040_, v_a_2041_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___boxed(lean_object* v_json_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_json_2104_, v_a_2105_);
lean_dec(v_json_2104_);
return v_res_2107_;
}
}
lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v___y_2113_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = l_List_reverse___redArg(v_x_2112_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___y_2113_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
else
{
lean_object* v_head_2121_; 
v_head_2121_ = lean_ctor_get(v_x_2111_, 0);
lean_inc(v_head_2121_);
if (lean_obj_tag(v_head_2121_) == 2)
{
lean_object* v_n_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2153_; 
v_n_2122_ = lean_ctor_get(v_head_2121_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_head_2121_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2124_ = v_head_2121_;
v_isShared_2125_ = v_isSharedCheck_2153_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_n_2122_);
lean_dec(v_head_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2153_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_tail_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2151_; 
v_tail_2126_ = lean_ctor_get(v_x_2111_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2111_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_x_2111_, 0);
lean_dec(v_unused_2152_);
v___x_2128_ = v_x_2111_;
v_isShared_2129_ = v_isSharedCheck_2151_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_tail_2126_);
lean_dec(v_x_2111_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2151_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_mantissa_2130_; lean_object* v_exponent_2131_; lean_object* v_natZero_2132_; lean_object* v_intZero_2133_; uint8_t v_isNeg_2134_; 
v_mantissa_2130_ = lean_ctor_get(v_n_2122_, 0);
lean_inc(v_mantissa_2130_);
v_exponent_2131_ = lean_ctor_get(v_n_2122_, 1);
lean_inc(v_exponent_2131_);
lean_dec_ref(v_n_2122_);
v_natZero_2132_ = lean_unsigned_to_nat(0u);
v_intZero_2133_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2134_ = lean_int_dec_lt(v_mantissa_2130_, v_intZero_2133_);
if (v_isNeg_2134_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_eq(v_exponent_2131_, v_natZero_2132_);
lean_dec(v_exponent_2131_);
if (v___x_2135_ == 0)
{
lean_dec(v_mantissa_2130_);
lean_del_object(v___x_2128_);
lean_dec(v_tail_2126_);
lean_del_object(v___x_2124_);
lean_dec_ref(v___y_2113_);
lean_dec(v_x_2112_);
goto v___jp_2115_;
}
else
{
lean_object* v_nameMap_2136_; lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_nameMap_2136_ = lean_ctor_get(v___y_2113_, 1);
v_a_2137_ = lean_nat_abs(v_mantissa_2130_);
lean_dec(v_mantissa_2130_);
v___x_2138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2138_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2141_; 
lean_dec(v_a_2137_);
lean_del_object(v___x_2124_);
v_val_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___x_2138_, 1);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_x_2112_);
lean_ctor_set(v___x_2128_, 0, v_val_2139_);
v___x_2141_ = v___x_2128_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_val_2139_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_x_2112_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v_x_2111_ = v_tail_2126_;
v_x_2112_ = v___x_2141_;
goto _start;
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v___x_2138_);
lean_del_object(v___x_2128_);
lean_dec(v_tail_2126_);
lean_dec_ref(v___y_2113_);
lean_dec(v_x_2112_);
v___x_2144_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2145_ = l_Nat_reprFast(v_a_2137_);
v___x_2146_ = lean_string_append(v___x_2144_, v___x_2145_);
lean_dec_ref(v___x_2145_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 18);
lean_ctor_set(v___x_2124_, 0, v___x_2146_);
v___x_2148_ = v___x_2124_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
}
}
else
{
lean_dec(v_exponent_2131_);
lean_dec(v_mantissa_2130_);
lean_del_object(v___x_2128_);
lean_dec(v_tail_2126_);
lean_del_object(v___x_2124_);
lean_dec_ref(v___y_2113_);
lean_dec(v_x_2112_);
goto v___jp_2115_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_2111_, 2);
lean_dec(v_head_2121_);
lean_dec_ref(v___y_2113_);
lean_dec(v_x_2112_);
goto v___jp_2115_;
}
}
v___jp_2115_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1));
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2111_ = stack[0].m_obj;
lean_object* v_x_2112_ = stack[1].m_obj;
lean_object* v___y_2113_ = stack[2].m_obj;
lean_object* v_res_2154_;
v_res_2154_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v_x_2111_, v_x_2112_, v___y_2113_);
stack->m_obj
 = v_res_2154_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___boxed(lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v_x_2155_, v_x_2156_, v___y_2157_);
return v_res_2159_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(lean_object* v_idxs_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_array_to_list(v_idxs_2160_);
v___x_2164_ = lean_box(0);
v___x_2165_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v___x_2163_, v___x_2164_, v_a_2161_);
return v___x_2165_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList_0interp(lean_interpreter_value* stack)
{
lean_object* v_idxs_2160_ = stack[0].m_obj;
lean_object* v_a_2161_ = stack[1].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_idxs_2160_, v_a_2161_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList___boxed(lean_object* v_idxs_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_idxs_2167_, v_a_2168_);
return v_res_2170_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(lean_object* v_a_2171_, lean_object* v_x_2172_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = 0;
return v___x_2173_;
}
else
{
lean_object* v_key_2174_; lean_object* v_tail_2175_; uint8_t v___x_2176_; 
v_key_2174_ = lean_ctor_get(v_x_2172_, 0);
v_tail_2175_ = lean_ctor_get(v_x_2172_, 2);
v___x_2176_ = lean_name_eq(v_key_2174_, v_a_2171_);
if (v___x_2176_ == 0)
{
v_x_2172_ = v_tail_2175_;
goto _start;
}
else
{
return v___x_2176_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2171_ = stack[0].m_obj;
lean_object* v_x_2172_ = stack[1].m_obj;
uint8_t v_res_2178_;
v_res_2178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2171_, v_x_2172_);
stack->m_num = v_res_2178_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_2179_, lean_object* v_x_2180_){
_start:
{
uint8_t v_res_2181_; lean_object* v_r_2182_; 
v_res_2181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2179_, v_x_2180_);
lean_dec(v_x_2180_);
lean_dec(v_a_2179_);
v_r_2182_ = lean_box(v_res_2181_);
return v_r_2182_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object* v_m_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_buckets_2185_; lean_object* v___x_2186_; uint64_t v___y_2188_; 
v_buckets_2185_ = lean_ctor_get(v_m_2183_, 1);
v___x_2186_ = lean_array_get_size(v_buckets_2185_);
if (lean_obj_tag(v_a_2184_) == 0)
{
uint64_t v___x_2202_; 
v___x_2202_ = 1723ULL;
v___y_2188_ = v___x_2202_;
goto v___jp_2187_;
}
else
{
uint64_t v_hash_2203_; 
v_hash_2203_ = lean_ctor_get_uint64(v_a_2184_, sizeof(void*)*2);
v___y_2188_ = v_hash_2203_;
goto v___jp_2187_;
}
v___jp_2187_:
{
uint64_t v___x_2189_; uint64_t v___x_2190_; uint64_t v_fold_2191_; uint64_t v___x_2192_; uint64_t v___x_2193_; uint64_t v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2189_ = 32ULL;
v___x_2190_ = lean_uint64_shift_right(v___y_2188_, v___x_2189_);
v_fold_2191_ = lean_uint64_xor(v___y_2188_, v___x_2190_);
v___x_2192_ = 16ULL;
v___x_2193_ = lean_uint64_shift_right(v_fold_2191_, v___x_2192_);
v___x_2194_ = lean_uint64_xor(v_fold_2191_, v___x_2193_);
v___x_2195_ = lean_uint64_to_usize(v___x_2194_);
v___x_2196_ = lean_usize_of_nat(v___x_2186_);
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = lean_usize_sub(v___x_2196_, v___x_2197_);
v___x_2199_ = lean_usize_land(v___x_2195_, v___x_2198_);
v___x_2200_ = lean_array_uget_borrowed(v_buckets_2185_, v___x_2199_);
v___x_2201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2184_, v___x_2200_);
return v___x_2201_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2183_ = stack[0].m_obj;
lean_object* v_a_2184_ = stack[1].m_obj;
uint8_t v_res_2204_;
v_res_2204_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2183_, v_a_2184_);
stack->m_num = v_res_2204_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg___boxed(lean_object* v_m_2205_, lean_object* v_a_2206_){
_start:
{
uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_res_2207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_m_2205_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
return v_x_2209_;
}
else
{
lean_object* v_key_2211_; lean_object* v_value_2212_; lean_object* v_tail_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2239_; 
v_key_2211_ = lean_ctor_get(v_x_2210_, 0);
v_value_2212_ = lean_ctor_get(v_x_2210_, 1);
v_tail_2213_ = lean_ctor_get(v_x_2210_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_x_2210_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2215_ = v_x_2210_;
v_isShared_2216_ = v_isSharedCheck_2239_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_tail_2213_);
lean_inc(v_value_2212_);
lean_inc(v_key_2211_);
lean_dec(v_x_2210_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2239_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; uint64_t v___y_2219_; 
v___x_2217_ = lean_array_get_size(v_x_2209_);
if (lean_obj_tag(v_key_2211_) == 0)
{
uint64_t v___x_2237_; 
v___x_2237_ = 1723ULL;
v___y_2219_ = v___x_2237_;
goto v___jp_2218_;
}
else
{
uint64_t v_hash_2238_; 
v_hash_2238_ = lean_ctor_get_uint64(v_key_2211_, sizeof(void*)*2);
v___y_2219_ = v_hash_2238_;
goto v___jp_2218_;
}
v___jp_2218_:
{
uint64_t v___x_2220_; uint64_t v___x_2221_; uint64_t v_fold_2222_; uint64_t v___x_2223_; uint64_t v___x_2224_; uint64_t v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2220_ = 32ULL;
v___x_2221_ = lean_uint64_shift_right(v___y_2219_, v___x_2220_);
v_fold_2222_ = lean_uint64_xor(v___y_2219_, v___x_2221_);
v___x_2223_ = 16ULL;
v___x_2224_ = lean_uint64_shift_right(v_fold_2222_, v___x_2223_);
v___x_2225_ = lean_uint64_xor(v_fold_2222_, v___x_2224_);
v___x_2226_ = lean_uint64_to_usize(v___x_2225_);
v___x_2227_ = lean_usize_of_nat(v___x_2217_);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_sub(v___x_2227_, v___x_2228_);
v___x_2230_ = lean_usize_land(v___x_2226_, v___x_2229_);
v___x_2231_ = lean_array_uget_borrowed(v_x_2209_, v___x_2230_);
lean_inc(v___x_2231_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 2, v___x_2231_);
v___x_2233_ = v___x_2215_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_key_2211_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_value_2212_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_array_uset(v_x_2209_, v___x_2230_, v___x_2233_);
v_x_2209_ = v___x_2234_;
v_x_2210_ = v_tail_2213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2240_, lean_object* v_source_2241_, lean_object* v_target_2242_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_array_get_size(v_source_2241_);
v___x_2244_ = lean_nat_dec_lt(v_i_2240_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec_ref(v_source_2241_);
lean_dec(v_i_2240_);
return v_target_2242_;
}
else
{
lean_object* v_es_2245_; lean_object* v___x_2246_; lean_object* v_source_2247_; lean_object* v_target_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_es_2245_ = lean_array_fget(v_source_2241_, v_i_2240_);
v___x_2246_ = lean_box(0);
v_source_2247_ = lean_array_fset(v_source_2241_, v_i_2240_, v___x_2246_);
v_target_2248_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2242_, v_es_2245_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v_i_2240_, v___x_2249_);
lean_dec(v_i_2240_);
v_i_2240_ = v___x_2250_;
v_source_2241_ = v_source_2247_;
v_target_2242_ = v_target_2248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(lean_object* v_data_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_nbuckets_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2253_ = lean_array_get_size(v_data_2252_);
v___x_2254_ = lean_unsigned_to_nat(2u);
v_nbuckets_2255_ = lean_nat_mul(v___x_2253_, v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_mk_array(v_nbuckets_2255_, v___x_2257_);
v___x_2259_ = lean_array_propagate_mark(v_data_2252_, v___x_2258_);
v___x_2260_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v___x_2256_, v_data_2252_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(lean_object* v_a_2261_, lean_object* v_b_2262_, lean_object* v_x_2263_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 0)
{
lean_dec(v_b_2262_);
lean_dec(v_a_2261_);
return v_x_2263_;
}
else
{
lean_object* v_key_2264_; lean_object* v_value_2265_; lean_object* v_tail_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2278_; 
v_key_2264_ = lean_ctor_get(v_x_2263_, 0);
v_value_2265_ = lean_ctor_get(v_x_2263_, 1);
v_tail_2266_ = lean_ctor_get(v_x_2263_, 2);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2268_ = v_x_2263_;
v_isShared_2269_ = v_isSharedCheck_2278_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_tail_2266_);
lean_inc(v_value_2265_);
lean_inc(v_key_2264_);
lean_dec(v_x_2263_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2278_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_name_eq(v_key_2264_, v_a_2261_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2261_, v_b_2262_, v_tail_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 2, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_key_2264_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_value_2265_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
else
{
lean_object* v___x_2276_; 
lean_dec(v_value_2265_);
lean_dec(v_key_2264_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_b_2262_);
lean_ctor_set(v___x_2268_, 0, v_a_2261_);
v___x_2276_ = v___x_2268_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2261_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_b_2262_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_tail_2266_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object* v_m_2279_, lean_object* v_a_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v_size_2282_; lean_object* v_buckets_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2329_; 
v_size_2282_ = lean_ctor_get(v_m_2279_, 0);
v_buckets_2283_ = lean_ctor_get(v_m_2279_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_m_2279_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2285_ = v_m_2279_;
v_isShared_2286_ = v_isSharedCheck_2329_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_buckets_2283_);
lean_inc(v_size_2282_);
lean_dec(v_m_2279_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2329_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; uint64_t v___y_2289_; 
v___x_2287_ = lean_array_get_size(v_buckets_2283_);
if (lean_obj_tag(v_a_2280_) == 0)
{
uint64_t v___x_2327_; 
v___x_2327_ = 1723ULL;
v___y_2289_ = v___x_2327_;
goto v___jp_2288_;
}
else
{
uint64_t v_hash_2328_; 
v_hash_2328_ = lean_ctor_get_uint64(v_a_2280_, sizeof(void*)*2);
v___y_2289_ = v_hash_2328_;
goto v___jp_2288_;
}
v___jp_2288_:
{
uint64_t v___x_2290_; uint64_t v___x_2291_; uint64_t v_fold_2292_; uint64_t v___x_2293_; uint64_t v___x_2294_; uint64_t v___x_2295_; size_t v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; size_t v___x_2299_; size_t v___x_2300_; lean_object* v_bkt_2301_; uint8_t v___x_2302_; 
v___x_2290_ = 32ULL;
v___x_2291_ = lean_uint64_shift_right(v___y_2289_, v___x_2290_);
v_fold_2292_ = lean_uint64_xor(v___y_2289_, v___x_2291_);
v___x_2293_ = 16ULL;
v___x_2294_ = lean_uint64_shift_right(v_fold_2292_, v___x_2293_);
v___x_2295_ = lean_uint64_xor(v_fold_2292_, v___x_2294_);
v___x_2296_ = lean_uint64_to_usize(v___x_2295_);
v___x_2297_ = lean_usize_of_nat(v___x_2287_);
v___x_2298_ = ((size_t)1ULL);
v___x_2299_ = lean_usize_sub(v___x_2297_, v___x_2298_);
v___x_2300_ = lean_usize_land(v___x_2296_, v___x_2299_);
v_bkt_2301_ = lean_array_uget_borrowed(v_buckets_2283_, v___x_2300_);
v___x_2302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2280_, v_bkt_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v_size_x27_2304_; lean_object* v___x_2305_; lean_object* v_buckets_x27_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
v_size_x27_2304_ = lean_nat_add(v_size_2282_, v___x_2303_);
lean_dec(v_size_2282_);
lean_inc(v_bkt_2301_);
v___x_2305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2280_);
lean_ctor_set(v___x_2305_, 1, v_b_2281_);
lean_ctor_set(v___x_2305_, 2, v_bkt_2301_);
v_buckets_x27_2306_ = lean_array_uset(v_buckets_2283_, v___x_2300_, v___x_2305_);
v___x_2307_ = lean_unsigned_to_nat(4u);
v___x_2308_ = lean_nat_mul(v_size_x27_2304_, v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(3u);
v___x_2310_ = lean_nat_div(v___x_2308_, v___x_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_array_get_size(v_buckets_x27_2306_);
v___x_2312_ = lean_nat_dec_le(v___x_2310_, v___x_2311_);
lean_dec(v___x_2310_);
if (v___x_2312_ == 0)
{
lean_object* v_val_2313_; lean_object* v___x_2315_; 
v_val_2313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_buckets_x27_2306_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v_val_2313_);
lean_ctor_set(v___x_2285_, 0, v_size_x27_2304_);
v___x_2315_ = v___x_2285_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_size_x27_2304_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_val_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
else
{
lean_object* v___x_2318_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v_buckets_x27_2306_);
lean_ctor_set(v___x_2285_, 0, v_size_x27_2304_);
v___x_2318_ = v___x_2285_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_size_x27_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_buckets_x27_2306_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v___x_2320_; lean_object* v_buckets_x27_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
lean_inc(v_bkt_2301_);
v___x_2320_ = lean_box(0);
v_buckets_x27_2321_ = lean_array_uset(v_buckets_2283_, v___x_2300_, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2280_, v_b_2281_, v_bkt_2301_);
v___x_2323_ = lean_array_uset(v_buckets_x27_2321_, v___x_2300_, v___x_2322_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2323_);
v___x_2325_ = v___x_2285_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_size_2282_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(lean_object* v_data_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2335_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 1)
{
lean_object* v_val_2352_; 
v_val_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2351_, 1);
if (lean_obj_tag(v_val_2352_) == 2)
{
lean_object* v_n_2353_; lean_object* v_mantissa_2354_; lean_object* v_exponent_2355_; lean_object* v_natZero_2356_; lean_object* v_intZero_2357_; uint8_t v_isNeg_2358_; 
v_n_2353_ = lean_ctor_get(v_val_2352_, 0);
lean_inc_ref(v_n_2353_);
lean_dec_ref_known(v_val_2352_, 1);
v_mantissa_2354_ = lean_ctor_get(v_n_2353_, 0);
lean_inc(v_mantissa_2354_);
v_exponent_2355_ = lean_ctor_get(v_n_2353_, 1);
lean_inc(v_exponent_2355_);
lean_dec_ref(v_n_2353_);
v_natZero_2356_ = lean_unsigned_to_nat(0u);
v_intZero_2357_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2358_ = lean_int_dec_lt(v_mantissa_2354_, v_intZero_2357_);
if (v_isNeg_2358_ == 0)
{
uint8_t v___x_2359_; 
v___x_2359_ = lean_nat_dec_eq(v_exponent_2355_, v_natZero_2356_);
lean_dec(v_exponent_2355_);
if (v___x_2359_ == 0)
{
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2338_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2335_, v___x_2360_);
if (lean_obj_tag(v___x_2361_) == 1)
{
lean_object* v_val_2362_; 
v_val_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v___x_2361_, 1);
if (lean_obj_tag(v_val_2362_) == 4)
{
lean_object* v_elems_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_elems_2363_ = lean_ctor_get(v_val_2362_, 0);
lean_inc_ref(v_elems_2363_);
lean_dec_ref_known(v_val_2362_, 1);
v___x_2364_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2365_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2335_, v___x_2364_);
if (lean_obj_tag(v___x_2365_) == 1)
{
lean_object* v_val_2366_; 
v_val_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v___x_2365_, 1);
if (lean_obj_tag(v_val_2366_) == 2)
{
lean_object* v_n_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2474_; 
v_n_2367_ = lean_ctor_get(v_val_2366_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_val_2366_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2369_ = v_val_2366_;
v_isShared_2370_ = v_isSharedCheck_2474_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_n_2367_);
lean_dec(v_val_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2474_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_mantissa_2371_; lean_object* v_exponent_2372_; uint8_t v_isNeg_2373_; 
v_mantissa_2371_ = lean_ctor_get(v_n_2367_, 0);
lean_inc(v_mantissa_2371_);
v_exponent_2372_ = lean_ctor_get(v_n_2367_, 1);
lean_inc(v_exponent_2372_);
lean_dec_ref(v_n_2367_);
v_isNeg_2373_ = lean_int_dec_lt(v_mantissa_2371_, v_intZero_2357_);
if (v_isNeg_2373_ == 0)
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_nat_dec_eq(v_exponent_2372_, v_natZero_2356_);
lean_dec(v_exponent_2372_);
if (v___x_2374_ == 0)
{
lean_dec(v_mantissa_2371_);
lean_del_object(v___x_2369_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2344_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_2376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2335_, v___x_2375_);
if (lean_obj_tag(v___x_2376_) == 1)
{
lean_object* v_val_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2473_; 
v_val_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2473_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_val_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2473_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
if (lean_obj_tag(v_val_2377_) == 1)
{
uint8_t v_b_2381_; lean_object* v_nameMap_2382_; lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_b_2381_ = lean_ctor_get_uint8(v_val_2377_, 0);
lean_dec_ref_known(v_val_2377_, 0);
v_nameMap_2382_ = lean_ctor_get(v_a_2336_, 1);
v_a_2383_ = lean_nat_abs(v_mantissa_2354_);
lean_dec(v_mantissa_2354_);
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2384_) == 1)
{
lean_object* v_val_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2383_);
lean_del_object(v___x_2379_);
lean_del_object(v___x_2369_);
v_val_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2463_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_val_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2463_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_nat_abs(v_mantissa_2371_);
lean_dec(v_mantissa_2371_);
v___x_2390_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2363_, v_a_2336_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2454_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2454_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2454_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_snd_2395_; lean_object* v_fst_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2453_; 
v_snd_2395_ = lean_ctor_get(v_a_2391_, 1);
v_fst_2396_ = lean_ctor_get(v_a_2391_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2391_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2398_ = v_a_2391_;
v_isShared_2399_ = v_isSharedCheck_2453_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_snd_2395_);
lean_inc(v_fst_2396_);
lean_dec(v_a_2391_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2453_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_stream_2400_; lean_object* v_nameMap_2401_; lean_object* v_levelMap_2402_; lean_object* v_exprMap_2403_; lean_object* v_recursorRuleMap_2404_; lean_object* v_constMap_2405_; lean_object* v_constOrder_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2452_; 
v_stream_2400_ = lean_ctor_get(v_snd_2395_, 0);
v_nameMap_2401_ = lean_ctor_get(v_snd_2395_, 1);
v_levelMap_2402_ = lean_ctor_get(v_snd_2395_, 2);
v_exprMap_2403_ = lean_ctor_get(v_snd_2395_, 3);
v_recursorRuleMap_2404_ = lean_ctor_get(v_snd_2395_, 4);
v_constMap_2405_ = lean_ctor_get(v_snd_2395_, 5);
v_constOrder_2406_ = lean_ctor_get(v_snd_2395_, 6);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_snd_2395_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2408_ = v_snd_2395_;
v_isShared_2409_ = v_isSharedCheck_2452_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_constOrder_2406_);
lean_inc(v_constMap_2405_);
lean_inc(v_recursorRuleMap_2404_);
lean_inc(v_exprMap_2403_);
lean_inc(v_levelMap_2402_);
lean_inc(v_nameMap_2401_);
lean_inc(v_stream_2400_);
lean_dec(v_snd_2395_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2452_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2403_, v_a_2389_);
if (lean_obj_tag(v___x_2410_) == 1)
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2389_);
lean_del_object(v___x_2387_);
v_val_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2442_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2442_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
lean_inc(v_val_2385_);
v___x_2415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2415_, 0, v_val_2385_);
lean_ctor_set(v___x_2415_, 1, v_fst_2396_);
lean_ctor_set(v___x_2415_, 2, v_val_2411_);
v___x_2416_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2405_, v_val_2385_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*1, v_b_2381_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2417_);
v___x_2419_ = v___x_2413_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2420_ = lean_box(0);
lean_inc(v_val_2385_);
v___x_2421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2405_, v_val_2385_, v___x_2419_);
v___x_2422_ = lean_array_push(v_constOrder_2406_, v_val_2385_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 6, v___x_2422_);
lean_ctor_set(v___x_2408_, 5, v___x_2421_);
v___x_2424_ = v___x_2408_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_stream_2400_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_nameMap_2401_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_levelMap_2402_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_exprMap_2403_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_recursorRuleMap_2404_);
lean_ctor_set(v_reuseFailAlloc_2431_, 5, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2431_, 6, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v___x_2424_);
lean_ctor_set(v___x_2398_, 0, v___x_2420_);
v___x_2426_ = v___x_2398_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2426_);
v___x_2428_ = v___x_2393_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec_ref_known(v___x_2415_, 3);
lean_del_object(v___x_2408_);
lean_dec_ref(v_constOrder_2406_);
lean_dec_ref(v_constMap_2405_);
lean_dec_ref(v_recursorRuleMap_2404_);
lean_dec_ref(v_exprMap_2403_);
lean_dec_ref(v_levelMap_2402_);
lean_dec_ref(v_nameMap_2401_);
lean_dec_ref(v_stream_2400_);
lean_del_object(v___x_2398_);
v___x_2433_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2434_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2385_, v___x_2416_);
v___x_2435_ = lean_string_append(v___x_2433_, v___x_2434_);
lean_dec_ref(v___x_2434_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 18);
lean_ctor_set(v___x_2413_, 0, v___x_2435_);
v___x_2437_ = v___x_2413_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2439_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2437_);
v___x_2439_ = v___x_2393_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v___x_2410_);
lean_del_object(v___x_2408_);
lean_dec_ref(v_constOrder_2406_);
lean_dec_ref(v_constMap_2405_);
lean_dec_ref(v_recursorRuleMap_2404_);
lean_dec_ref(v_exprMap_2403_);
lean_dec_ref(v_levelMap_2402_);
lean_dec_ref(v_nameMap_2401_);
lean_dec_ref(v_stream_2400_);
lean_del_object(v___x_2398_);
lean_dec(v_fst_2396_);
lean_dec(v_val_2385_);
v___x_2443_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2444_ = l_Nat_reprFast(v_a_2389_);
v___x_2445_ = lean_string_append(v___x_2443_, v___x_2444_);
lean_dec_ref(v___x_2444_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 18);
lean_ctor_set(v___x_2387_, 0, v___x_2445_);
v___x_2447_ = v___x_2387_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2449_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2447_);
v___x_2449_ = v___x_2393_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_a_2389_);
lean_del_object(v___x_2387_);
lean_dec(v_val_2385_);
v_a_2455_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2390_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2390_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
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
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v___x_2384_);
lean_dec(v_mantissa_2371_);
lean_dec_ref(v_elems_2363_);
lean_dec_ref(v_a_2336_);
v___x_2464_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2465_ = l_Nat_reprFast(v_a_2383_);
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
lean_dec_ref(v___x_2465_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 18);
lean_ctor_set(v___x_2379_, 0, v___x_2466_);
v___x_2468_ = v___x_2379_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set_tag(v___x_2369_, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2468_);
v___x_2470_ = v___x_2369_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec(v_mantissa_2371_);
lean_del_object(v___x_2369_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2347_;
}
}
}
else
{
lean_dec(v___x_2376_);
lean_dec(v_mantissa_2371_);
lean_del_object(v___x_2369_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2347_;
}
}
}
else
{
lean_dec(v_exponent_2372_);
lean_dec(v_mantissa_2371_);
lean_del_object(v___x_2369_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2344_;
}
}
}
else
{
lean_dec(v_val_2366_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2344_;
}
}
else
{
lean_dec(v___x_2365_);
lean_dec_ref(v_elems_2363_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2344_;
}
}
else
{
lean_dec(v_val_2362_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2341_;
}
}
else
{
lean_dec(v___x_2361_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2341_;
}
}
}
else
{
lean_dec(v_exponent_2355_);
lean_dec(v_mantissa_2354_);
lean_dec_ref(v_a_2336_);
goto v___jp_2338_;
}
}
else
{
lean_dec(v_val_2352_);
lean_dec_ref(v_a_2336_);
goto v___jp_2338_;
}
}
else
{
lean_dec(v___x_2351_);
lean_dec_ref(v_a_2336_);
goto v___jp_2338_;
}
v___jp_2338_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
return v___x_2340_;
}
v___jp_2341_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
v___jp_2344_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
v___jp_2347_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_2335_ = stack[0].m_obj;
lean_object* v_a_2336_ = stack[1].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_data_2335_, v_a_2336_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___boxed(lean_object* v_data_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_data_2476_, v_a_2477_);
lean_dec(v_data_2476_);
return v_res_2479_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_object* v_00_u03b2_2480_, lean_object* v_m_2481_, lean_object* v_a_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2481_, v_a_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2481_ = stack[1].m_obj;
lean_object* v_a_2482_ = stack[2].m_obj;
uint8_t v_res_2484_;
v_res_2484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_box(0), v_m_2481_, v_a_2482_);
stack->m_num = v_res_2484_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___boxed(lean_object* v_00_u03b2_2485_, lean_object* v_m_2486_, lean_object* v_a_2487_){
_start:
{
uint8_t v_res_2488_; lean_object* v_r_2489_; 
v_res_2488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(v_00_u03b2_2485_, v_m_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_m_2486_);
v_r_2489_ = lean_box(v_res_2488_);
return v_r_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1(lean_object* v_00_u03b2_2490_, lean_object* v_m_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_m_2491_, v_a_2492_, v_b_2493_);
return v___x_2494_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_object* v_00_u03b2_2495_, lean_object* v_a_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2496_, v_x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2496_ = stack[1].m_obj;
lean_object* v_x_2497_ = stack[2].m_obj;
uint8_t v_res_2499_;
v_res_2499_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_box(0), v_a_2496_, v_x_2497_);
stack->m_num = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2500_, lean_object* v_a_2501_, lean_object* v_x_2502_){
_start:
{
uint8_t v_res_2503_; lean_object* v_r_2504_; 
v_res_2503_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(v_00_u03b2_2500_, v_a_2501_, v_x_2502_);
lean_dec(v_x_2502_);
lean_dec(v_a_2501_);
v_r_2504_ = lean_box(v_res_2503_);
return v_r_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2(lean_object* v_00_u03b2_2505_, lean_object* v_data_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_data_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3(lean_object* v_00_u03b2_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2509_, v_b_2510_, v_x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2513_, lean_object* v_i_2514_, lean_object* v_source_2515_, lean_object* v_target_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v_i_2514_, v_source_2515_, v_target_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2519_, v_x_2520_);
return v___x_2521_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(lean_object* v_data_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2562_);
if (lean_obj_tag(v___x_2563_) == 1)
{
lean_object* v_val_2564_; 
v_val_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v___x_2563_, 1);
if (lean_obj_tag(v_val_2564_) == 2)
{
lean_object* v_n_2565_; lean_object* v_mantissa_2566_; lean_object* v_exponent_2567_; lean_object* v_natZero_2568_; lean_object* v_intZero_2569_; uint8_t v_isNeg_2570_; 
v_n_2565_ = lean_ctor_get(v_val_2564_, 0);
lean_inc_ref(v_n_2565_);
lean_dec_ref_known(v_val_2564_, 1);
v_mantissa_2566_ = lean_ctor_get(v_n_2565_, 0);
lean_inc(v_mantissa_2566_);
v_exponent_2567_ = lean_ctor_get(v_n_2565_, 1);
lean_inc(v_exponent_2567_);
lean_dec_ref(v_n_2565_);
v_natZero_2568_ = lean_unsigned_to_nat(0u);
v_intZero_2569_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2570_ = lean_int_dec_lt(v_mantissa_2566_, v_intZero_2569_);
if (v_isNeg_2570_ == 0)
{
uint8_t v___x_2571_; 
v___x_2571_ = lean_nat_dec_eq(v_exponent_2567_, v_natZero_2568_);
lean_dec(v_exponent_2567_);
if (v___x_2571_ == 0)
{
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2538_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2572_);
if (lean_obj_tag(v___x_2573_) == 1)
{
lean_object* v_val_2574_; 
v_val_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (lean_obj_tag(v_val_2574_) == 4)
{
lean_object* v_elems_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_elems_2575_ = lean_ctor_get(v_val_2574_, 0);
lean_inc_ref(v_elems_2575_);
lean_dec_ref_known(v_val_2574_, 1);
v___x_2576_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2576_);
if (lean_obj_tag(v___x_2577_) == 1)
{
lean_object* v_val_2578_; 
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2577_, 1);
if (lean_obj_tag(v_val_2578_) == 2)
{
lean_object* v_n_2579_; lean_object* v_mantissa_2580_; lean_object* v_exponent_2581_; uint8_t v_isNeg_2582_; 
v_n_2579_ = lean_ctor_get(v_val_2578_, 0);
lean_inc_ref(v_n_2579_);
lean_dec_ref_known(v_val_2578_, 1);
v_mantissa_2580_ = lean_ctor_get(v_n_2579_, 0);
lean_inc(v_mantissa_2580_);
v_exponent_2581_ = lean_ctor_get(v_n_2579_, 1);
lean_inc(v_exponent_2581_);
lean_dec_ref(v_n_2579_);
v_isNeg_2582_ = lean_int_dec_lt(v_mantissa_2580_, v_intZero_2569_);
if (v_isNeg_2582_ == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_nat_dec_eq(v_exponent_2581_, v_natZero_2568_);
lean_dec(v_exponent_2581_);
if (v___x_2583_ == 0)
{
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2544_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 1)
{
lean_object* v_val_2586_; 
v_val_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2585_, 1);
if (lean_obj_tag(v_val_2586_) == 2)
{
lean_object* v_n_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2785_; 
v_n_2587_ = lean_ctor_get(v_val_2586_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_val_2586_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2589_ = v_val_2586_;
v_isShared_2590_ = v_isSharedCheck_2785_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_n_2587_);
lean_dec(v_val_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2785_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_mantissa_2591_; lean_object* v_exponent_2592_; uint8_t v_isNeg_2593_; 
v_mantissa_2591_ = lean_ctor_get(v_n_2587_, 0);
lean_inc(v_mantissa_2591_);
v_exponent_2592_ = lean_ctor_get(v_n_2587_, 1);
lean_inc(v_exponent_2592_);
lean_dec_ref(v_n_2587_);
v_isNeg_2593_ = lean_int_dec_lt(v_mantissa_2591_, v_intZero_2569_);
if (v_isNeg_2593_ == 0)
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_nat_dec_eq(v_exponent_2592_, v_natZero_2568_);
lean_dec(v_exponent_2592_);
if (v___x_2594_ == 0)
{
lean_dec(v_mantissa_2591_);
lean_del_object(v___x_2589_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2547_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2));
v___x_2596_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2595_);
if (lean_obj_tag(v___x_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_del_object(v___x_2589_);
v_val_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3));
v___x_2599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 1)
{
lean_object* v_val_2600_; 
v_val_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_val_2600_);
lean_dec_ref_known(v___x_2599_, 1);
if (lean_obj_tag(v_val_2600_) == 3)
{
lean_object* v_s_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_s_2601_ = lean_ctor_get(v_val_2600_, 0);
lean_inc_ref(v_s_2601_);
lean_dec_ref_known(v_val_2600_, 1);
v___x_2602_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2535_, v___x_2602_);
if (lean_obj_tag(v___x_2603_) == 1)
{
lean_object* v_val_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2780_; 
v_val_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2780_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_val_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2780_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
if (lean_obj_tag(v_val_2604_) == 4)
{
lean_object* v_elems_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2779_; 
v_elems_2608_ = lean_ctor_get(v_val_2604_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_val_2604_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2610_ = v_val_2604_;
v_isShared_2611_ = v_isSharedCheck_2779_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_elems_2608_);
lean_dec(v_val_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2779_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_nameMap_2612_; lean_object* v_a_2613_; lean_object* v___x_2614_; 
v_nameMap_2612_ = lean_ctor_get(v_a_2536_, 1);
v_a_2613_ = lean_nat_abs(v_mantissa_2566_);
lean_dec(v_mantissa_2566_);
v___x_2614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2612_, v_a_2613_);
if (lean_obj_tag(v___x_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2613_);
lean_del_object(v___x_2610_);
lean_del_object(v___x_2606_);
v_val_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2769_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_val_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2769_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_a_2619_; lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2619_ = lean_nat_abs(v_mantissa_2580_);
lean_dec(v_mantissa_2580_);
v_a_2620_ = lean_nat_abs(v_mantissa_2591_);
lean_dec(v_mantissa_2591_);
v___x_2621_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2575_, v_a_2536_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2760_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2760_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2760_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_snd_2626_; lean_object* v_fst_2627_; lean_object* v_exprMap_2628_; lean_object* v___x_2629_; 
v_snd_2626_ = lean_ctor_get(v_a_2622_, 1);
lean_inc(v_snd_2626_);
v_fst_2627_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_fst_2627_);
lean_dec(v_a_2622_);
v_exprMap_2628_ = lean_ctor_get(v_snd_2626_, 3);
v___x_2629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2628_, v_a_2619_);
if (lean_obj_tag(v___x_2629_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2619_);
lean_del_object(v___x_2617_);
v_val_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2750_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_val_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2750_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2628_, v_a_2620_);
if (lean_obj_tag(v___x_2634_) == 1)
{
lean_object* v_val_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_a_2620_);
v_val_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2740_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_val_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2740_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___y_2640_; uint8_t v_safety_2641_; lean_object* v___y_2642_; lean_object* v_hints_2702_; lean_object* v___y_2703_; 
switch(lean_obj_tag(v_val_2597_))
{
case 3:
{
lean_object* v_s_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_s_2721_ = lean_ctor_get(v_val_2597_, 0);
lean_inc_ref(v_s_2721_);
lean_dec_ref_known(v_val_2597_, 1);
v___x_2722_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_2723_ = lean_string_dec_eq(v_s_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10));
v___x_2725_ = lean_string_dec_eq(v_s_2721_, v___x_2724_);
lean_dec_ref(v_s_2721_);
if (v___x_2725_ == 0)
{
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
goto v___jp_2559_;
}
else
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_box(1);
v_hints_2702_ = v___x_2726_;
v___y_2703_ = v_snd_2626_;
goto v___jp_2701_;
}
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_s_2721_);
v___x_2727_ = lean_box(0);
v_hints_2702_ = v___x_2727_;
v___y_2703_ = v_snd_2626_;
goto v___jp_2701_;
}
}
case 5:
{
lean_object* v_kvPairs_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_kvPairs_2728_ = lean_ctor_get(v_val_2597_, 0);
lean_inc(v_kvPairs_2728_);
lean_dec_ref_known(v_val_2597_, 1);
v___x_2729_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11));
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2728_, v___x_2729_);
lean_dec(v_kvPairs_2728_);
if (lean_obj_tag(v___x_2730_) == 1)
{
lean_object* v_val_2731_; 
v_val_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_val_2731_);
lean_dec_ref_known(v___x_2730_, 1);
if (lean_obj_tag(v_val_2731_) == 2)
{
lean_object* v_n_2732_; lean_object* v_mantissa_2733_; lean_object* v_exponent_2734_; uint8_t v_isNeg_2735_; 
v_n_2732_ = lean_ctor_get(v_val_2731_, 0);
lean_inc_ref(v_n_2732_);
lean_dec_ref_known(v_val_2731_, 1);
v_mantissa_2733_ = lean_ctor_get(v_n_2732_, 0);
lean_inc(v_mantissa_2733_);
v_exponent_2734_ = lean_ctor_get(v_n_2732_, 1);
lean_inc(v_exponent_2734_);
lean_dec_ref(v_n_2732_);
v_isNeg_2735_ = lean_int_dec_lt(v_mantissa_2733_, v_intZero_2569_);
if (v_isNeg_2735_ == 0)
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_nat_dec_eq(v_exponent_2734_, v_natZero_2568_);
lean_dec(v_exponent_2734_);
if (v___x_2736_ == 0)
{
lean_dec(v_mantissa_2733_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
goto v___jp_2556_;
}
else
{
lean_object* v_a_2737_; uint32_t v___x_2738_; lean_object* v___x_2739_; 
v_a_2737_ = lean_nat_abs(v_mantissa_2733_);
lean_dec(v_mantissa_2733_);
v___x_2738_ = lean_uint32_of_nat(v_a_2737_);
lean_dec(v_a_2737_);
v___x_2739_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_2739_, 0, v___x_2738_);
v_hints_2702_ = v___x_2739_;
v___y_2703_ = v_snd_2626_;
goto v___jp_2701_;
}
}
else
{
lean_dec(v_exponent_2734_);
lean_dec(v_mantissa_2733_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
goto v___jp_2556_;
}
}
else
{
lean_dec(v_val_2731_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
goto v___jp_2556_;
}
}
else
{
lean_dec(v___x_2730_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
goto v___jp_2556_;
}
}
default: 
{
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_del_object(v___x_2624_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
goto v___jp_2559_;
}
}
v___jp_2639_:
{
lean_object* v___x_2643_; 
v___x_2643_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2608_, v___y_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2692_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2692_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2692_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_snd_2648_; lean_object* v_fst_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2691_; 
v_snd_2648_ = lean_ctor_get(v_a_2644_, 1);
v_fst_2649_ = lean_ctor_get(v_a_2644_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2651_ = v_a_2644_;
v_isShared_2652_ = v_isSharedCheck_2691_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_snd_2648_);
lean_inc(v_fst_2649_);
lean_dec(v_a_2644_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2691_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_stream_2653_; lean_object* v_nameMap_2654_; lean_object* v_levelMap_2655_; lean_object* v_exprMap_2656_; lean_object* v_recursorRuleMap_2657_; lean_object* v_constMap_2658_; lean_object* v_constOrder_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2690_; 
v_stream_2653_ = lean_ctor_get(v_snd_2648_, 0);
v_nameMap_2654_ = lean_ctor_get(v_snd_2648_, 1);
v_levelMap_2655_ = lean_ctor_get(v_snd_2648_, 2);
v_exprMap_2656_ = lean_ctor_get(v_snd_2648_, 3);
v_recursorRuleMap_2657_ = lean_ctor_get(v_snd_2648_, 4);
v_constMap_2658_ = lean_ctor_get(v_snd_2648_, 5);
v_constOrder_2659_ = lean_ctor_get(v_snd_2648_, 6);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_snd_2648_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2661_ = v_snd_2648_;
v_isShared_2662_ = v_isSharedCheck_2690_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_constOrder_2659_);
lean_inc(v_constMap_2658_);
lean_inc(v_recursorRuleMap_2657_);
lean_inc(v_exprMap_2656_);
lean_inc(v_levelMap_2655_);
lean_inc(v_nameMap_2654_);
lean_inc(v_stream_2653_);
lean_dec(v_snd_2648_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2690_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2658_, v_val_2615_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_inc(v_val_2615_);
v___x_2664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2664_, 0, v_val_2615_);
lean_ctor_set(v___x_2664_, 1, v_fst_2627_);
lean_ctor_set(v___x_2664_, 2, v_val_2630_);
v___x_2665_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v_val_2635_);
lean_ctor_set(v___x_2665_, 2, v___y_2640_);
lean_ctor_set(v___x_2665_, 3, v_fst_2649_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*4, v_safety_2641_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2665_);
v___x_2667_ = v___x_2637_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2668_ = lean_box(0);
lean_inc(v_val_2615_);
v___x_2669_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2658_, v_val_2615_, v___x_2667_);
v___x_2670_ = lean_array_push(v_constOrder_2659_, v_val_2615_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 6, v___x_2670_);
lean_ctor_set(v___x_2661_, 5, v___x_2669_);
v___x_2672_ = v___x_2661_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_stream_2653_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_nameMap_2654_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_levelMap_2655_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_exprMap_2656_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_recursorRuleMap_2657_);
lean_ctor_set(v_reuseFailAlloc_2679_, 5, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2679_, 6, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2672_);
lean_ctor_set(v___x_2651_, 0, v___x_2668_);
v___x_2674_ = v___x_2651_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2674_);
v___x_2676_ = v___x_2646_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
lean_del_object(v___x_2661_);
lean_dec_ref(v_constOrder_2659_);
lean_dec_ref(v_constMap_2658_);
lean_dec_ref(v_recursorRuleMap_2657_);
lean_dec_ref(v_exprMap_2656_);
lean_dec_ref(v_levelMap_2655_);
lean_dec_ref(v_nameMap_2654_);
lean_dec_ref(v_stream_2653_);
lean_del_object(v___x_2651_);
lean_dec(v_fst_2649_);
lean_dec(v___y_2640_);
lean_dec(v_val_2635_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
v___x_2681_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2615_, v___x_2663_);
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
lean_dec_ref(v___x_2682_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 18);
lean_ctor_set(v___x_2637_, 0, v___x_2683_);
v___x_2685_ = v___x_2637_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v___x_2685_);
v___x_2687_ = v___x_2646_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v___y_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_val_2615_);
v_a_2693_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2643_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2643_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
v___jp_2701_:
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5));
v___x_2705_ = lean_string_dec_eq(v_s_2601_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6));
v___x_2707_ = lean_string_dec_eq(v_s_2601_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7));
v___x_2709_ = lean_string_dec_eq(v_s_2601_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_dec_ref(v___y_2703_);
lean_dec(v_hints_2702_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
v___x_2710_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8));
v___x_2711_ = lean_string_append(v___x_2710_, v_s_2601_);
lean_dec_ref(v_s_2601_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 18);
lean_ctor_set(v___x_2632_, 0, v___x_2711_);
v___x_2713_ = v___x_2632_;
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
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2713_);
v___x_2715_ = v___x_2624_;
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
else
{
uint8_t v___x_2718_; 
lean_del_object(v___x_2632_);
lean_del_object(v___x_2624_);
lean_dec_ref(v_s_2601_);
v___x_2718_ = 2;
v___y_2640_ = v_hints_2702_;
v_safety_2641_ = v___x_2718_;
v___y_2642_ = v___y_2703_;
goto v___jp_2639_;
}
}
else
{
uint8_t v___x_2719_; 
lean_del_object(v___x_2632_);
lean_del_object(v___x_2624_);
lean_dec_ref(v_s_2601_);
v___x_2719_ = 1;
v___y_2640_ = v_hints_2702_;
v_safety_2641_ = v___x_2719_;
v___y_2642_ = v___y_2703_;
goto v___jp_2639_;
}
}
else
{
uint8_t v___x_2720_; 
lean_del_object(v___x_2632_);
lean_del_object(v___x_2624_);
lean_dec_ref(v_s_2601_);
v___x_2720_ = 0;
v___y_2640_ = v_hints_2702_;
v_safety_2641_ = v___x_2720_;
v___y_2642_ = v___y_2703_;
goto v___jp_2639_;
}
}
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
lean_dec(v___x_2634_);
lean_dec(v_val_2630_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
v___x_2741_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2742_ = l_Nat_reprFast(v_a_2620_);
v___x_2743_ = lean_string_append(v___x_2741_, v___x_2742_);
lean_dec_ref(v___x_2742_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 18);
lean_ctor_set(v___x_2632_, 0, v___x_2743_);
v___x_2745_ = v___x_2632_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2747_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2745_);
v___x_2747_ = v___x_2624_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec(v___x_2629_);
lean_dec(v_fst_2627_);
lean_dec(v_snd_2626_);
lean_dec(v_a_2620_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
v___x_2751_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2752_ = l_Nat_reprFast(v_a_2619_);
v___x_2753_ = lean_string_append(v___x_2751_, v___x_2752_);
lean_dec_ref(v___x_2752_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 18);
lean_ctor_set(v___x_2617_, 0, v___x_2753_);
v___x_2755_ = v___x_2617_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2757_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2755_);
v___x_2757_ = v___x_2624_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2620_);
lean_dec(v_a_2619_);
lean_del_object(v___x_2617_);
lean_dec(v_val_2615_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
v_a_2761_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2621_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2621_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v___x_2614_);
lean_dec_ref(v_elems_2608_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec_ref(v_a_2536_);
v___x_2770_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2771_ = l_Nat_reprFast(v_a_2613_);
v___x_2772_ = lean_string_append(v___x_2770_, v___x_2771_);
lean_dec_ref(v___x_2771_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 18);
lean_ctor_set(v___x_2610_, 0, v___x_2772_);
v___x_2774_ = v___x_2610_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2774_);
v___x_2776_ = v___x_2606_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
else
{
lean_del_object(v___x_2606_);
lean_dec(v_val_2604_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2553_;
}
}
}
else
{
lean_dec(v___x_2603_);
lean_dec_ref(v_s_2601_);
lean_dec(v_val_2597_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2553_;
}
}
else
{
lean_dec(v_val_2600_);
lean_dec(v_val_2597_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2550_;
}
}
else
{
lean_dec(v___x_2599_);
lean_dec(v_val_2597_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2550_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
lean_dec(v___x_2596_);
lean_dec(v_mantissa_2591_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
v___x_2781_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2781_);
v___x_2783_ = v___x_2589_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_dec(v_exponent_2592_);
lean_dec(v_mantissa_2591_);
lean_del_object(v___x_2589_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2547_;
}
}
}
else
{
lean_dec(v_val_2586_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2547_;
}
}
else
{
lean_dec(v___x_2585_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2547_;
}
}
}
else
{
lean_dec(v_exponent_2581_);
lean_dec(v_mantissa_2580_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2544_;
}
}
else
{
lean_dec(v_val_2578_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2544_;
}
}
else
{
lean_dec(v___x_2577_);
lean_dec_ref(v_elems_2575_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2544_;
}
}
else
{
lean_dec(v_val_2574_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2541_;
}
}
else
{
lean_dec(v___x_2573_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2541_;
}
}
}
else
{
lean_dec(v_exponent_2567_);
lean_dec(v_mantissa_2566_);
lean_dec_ref(v_a_2536_);
goto v___jp_2538_;
}
}
else
{
lean_dec(v_val_2564_);
lean_dec_ref(v_a_2536_);
goto v___jp_2538_;
}
}
else
{
lean_dec(v___x_2563_);
lean_dec_ref(v_a_2536_);
goto v___jp_2538_;
}
v___jp_2538_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
v___jp_2541_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
v___jp_2544_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
v___jp_2547_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
v___jp_2553_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
v___jp_2556_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
v___jp_2559_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_2535_ = stack[0].m_obj;
lean_object* v_a_2536_ = stack[1].m_obj;
lean_object* v_res_2786_;
v_res_2786_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_data_2535_, v_a_2536_);
stack->m_obj
 = v_res_2786_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___boxed(lean_object* v_data_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_data_2787_, v_a_2788_);
lean_dec(v_data_2787_);
return v_res_2790_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(lean_object* v_data_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2794_, v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 1)
{
lean_object* v_val_2814_; 
v_val_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v___x_2813_, 1);
if (lean_obj_tag(v_val_2814_) == 2)
{
lean_object* v_n_2815_; lean_object* v_mantissa_2816_; lean_object* v_exponent_2817_; lean_object* v_natZero_2818_; lean_object* v_intZero_2819_; uint8_t v_isNeg_2820_; 
v_n_2815_ = lean_ctor_get(v_val_2814_, 0);
lean_inc_ref(v_n_2815_);
lean_dec_ref_known(v_val_2814_, 1);
v_mantissa_2816_ = lean_ctor_get(v_n_2815_, 0);
lean_inc(v_mantissa_2816_);
v_exponent_2817_ = lean_ctor_get(v_n_2815_, 1);
lean_inc(v_exponent_2817_);
lean_dec_ref(v_n_2815_);
v_natZero_2818_ = lean_unsigned_to_nat(0u);
v_intZero_2819_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2820_ = lean_int_dec_lt(v_mantissa_2816_, v_intZero_2819_);
if (v_isNeg_2820_ == 0)
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_nat_dec_eq(v_exponent_2817_, v_natZero_2818_);
lean_dec(v_exponent_2817_);
if (v___x_2821_ == 0)
{
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2797_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2823_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2794_, v___x_2822_);
if (lean_obj_tag(v___x_2823_) == 1)
{
lean_object* v_val_2824_; 
v_val_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v___x_2823_, 1);
if (lean_obj_tag(v_val_2824_) == 4)
{
lean_object* v_elems_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_elems_2825_ = lean_ctor_get(v_val_2824_, 0);
lean_inc_ref(v_elems_2825_);
lean_dec_ref_known(v_val_2824_, 1);
v___x_2826_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2794_, v___x_2826_);
if (lean_obj_tag(v___x_2827_) == 1)
{
lean_object* v_val_2828_; 
v_val_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v___x_2827_, 1);
if (lean_obj_tag(v_val_2828_) == 2)
{
lean_object* v_n_2829_; lean_object* v_mantissa_2830_; lean_object* v_exponent_2831_; uint8_t v_isNeg_2832_; 
v_n_2829_ = lean_ctor_get(v_val_2828_, 0);
lean_inc_ref(v_n_2829_);
lean_dec_ref_known(v_val_2828_, 1);
v_mantissa_2830_ = lean_ctor_get(v_n_2829_, 0);
lean_inc(v_mantissa_2830_);
v_exponent_2831_ = lean_ctor_get(v_n_2829_, 1);
lean_inc(v_exponent_2831_);
lean_dec_ref(v_n_2829_);
v_isNeg_2832_ = lean_int_dec_lt(v_mantissa_2830_, v_intZero_2819_);
if (v_isNeg_2832_ == 0)
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_nat_dec_eq(v_exponent_2831_, v_natZero_2818_);
lean_dec(v_exponent_2831_);
if (v___x_2833_ == 0)
{
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2803_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2794_, v___x_2834_);
if (lean_obj_tag(v___x_2835_) == 1)
{
lean_object* v_val_2836_; 
v_val_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v___x_2835_, 1);
if (lean_obj_tag(v_val_2836_) == 2)
{
lean_object* v_n_2837_; lean_object* v_mantissa_2838_; lean_object* v_exponent_2839_; uint8_t v_isNeg_2840_; 
v_n_2837_ = lean_ctor_get(v_val_2836_, 0);
lean_inc_ref(v_n_2837_);
lean_dec_ref_known(v_val_2836_, 1);
v_mantissa_2838_ = lean_ctor_get(v_n_2837_, 0);
lean_inc(v_mantissa_2838_);
v_exponent_2839_ = lean_ctor_get(v_n_2837_, 1);
lean_inc(v_exponent_2839_);
lean_dec_ref(v_n_2837_);
v_isNeg_2840_ = lean_int_dec_lt(v_mantissa_2838_, v_intZero_2819_);
if (v_isNeg_2840_ == 0)
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_eq(v_exponent_2839_, v_natZero_2818_);
lean_dec(v_exponent_2839_);
if (v___x_2841_ == 0)
{
lean_dec(v_mantissa_2838_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2806_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2794_, v___x_2842_);
if (lean_obj_tag(v___x_2843_) == 1)
{
lean_object* v_val_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2977_; 
v_val_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2977_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_val_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2977_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_val_2844_) == 4)
{
lean_object* v_elems_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2976_; 
v_elems_2848_ = lean_ctor_get(v_val_2844_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_val_2844_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2850_ = v_val_2844_;
v_isShared_2851_ = v_isSharedCheck_2976_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_elems_2848_);
lean_dec(v_val_2844_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2976_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_nameMap_2852_; lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_nameMap_2852_ = lean_ctor_get(v_a_2795_, 1);
v_a_2853_ = lean_nat_abs(v_mantissa_2816_);
lean_dec(v_mantissa_2816_);
v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2852_, v_a_2853_);
if (lean_obj_tag(v___x_2854_) == 1)
{
lean_object* v_val_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2853_);
lean_del_object(v___x_2850_);
lean_del_object(v___x_2846_);
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2966_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_val_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2966_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2859_ = lean_nat_abs(v_mantissa_2830_);
lean_dec(v_mantissa_2830_);
v_a_2860_ = lean_nat_abs(v_mantissa_2838_);
lean_dec(v_mantissa_2838_);
v___x_2861_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2825_, v_a_2795_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2957_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2957_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2957_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_snd_2866_; lean_object* v_fst_2867_; lean_object* v_exprMap_2868_; lean_object* v___x_2869_; 
v_snd_2866_ = lean_ctor_get(v_a_2862_, 1);
lean_inc(v_snd_2866_);
v_fst_2867_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_fst_2867_);
lean_dec(v_a_2862_);
v_exprMap_2868_ = lean_ctor_get(v_snd_2866_, 3);
v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2868_, v_a_2859_);
if (lean_obj_tag(v___x_2869_) == 1)
{
lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2859_);
lean_del_object(v___x_2857_);
v_val_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2947_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2947_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2868_, v_a_2860_);
if (lean_obj_tag(v___x_2874_) == 1)
{
lean_object* v_val_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2937_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2864_);
lean_dec(v_a_2860_);
v_val_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2937_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_val_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2937_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; 
v___x_2879_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2848_, v_snd_2866_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2928_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2928_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2928_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_snd_2884_; lean_object* v_fst_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2927_; 
v_snd_2884_ = lean_ctor_get(v_a_2880_, 1);
v_fst_2885_ = lean_ctor_get(v_a_2880_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_a_2880_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2887_ = v_a_2880_;
v_isShared_2888_ = v_isSharedCheck_2927_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snd_2884_);
lean_inc(v_fst_2885_);
lean_dec(v_a_2880_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2927_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_stream_2889_; lean_object* v_nameMap_2890_; lean_object* v_levelMap_2891_; lean_object* v_exprMap_2892_; lean_object* v_recursorRuleMap_2893_; lean_object* v_constMap_2894_; lean_object* v_constOrder_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2926_; 
v_stream_2889_ = lean_ctor_get(v_snd_2884_, 0);
v_nameMap_2890_ = lean_ctor_get(v_snd_2884_, 1);
v_levelMap_2891_ = lean_ctor_get(v_snd_2884_, 2);
v_exprMap_2892_ = lean_ctor_get(v_snd_2884_, 3);
v_recursorRuleMap_2893_ = lean_ctor_get(v_snd_2884_, 4);
v_constMap_2894_ = lean_ctor_get(v_snd_2884_, 5);
v_constOrder_2895_ = lean_ctor_get(v_snd_2884_, 6);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_snd_2884_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2897_ = v_snd_2884_;
v_isShared_2898_ = v_isSharedCheck_2926_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_constOrder_2895_);
lean_inc(v_constMap_2894_);
lean_inc(v_recursorRuleMap_2893_);
lean_inc(v_exprMap_2892_);
lean_inc(v_levelMap_2891_);
lean_inc(v_nameMap_2890_);
lean_inc(v_stream_2889_);
lean_dec(v_snd_2884_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2926_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
uint8_t v___x_2899_; 
v___x_2899_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2894_, v_val_2855_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_inc(v_val_2855_);
v___x_2900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2900_, 0, v_val_2855_);
lean_ctor_set(v___x_2900_, 1, v_fst_2867_);
lean_ctor_set(v___x_2900_, 2, v_val_2870_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v_val_2875_);
lean_ctor_set(v___x_2901_, 2, v_fst_2885_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 2);
lean_ctor_set(v___x_2877_, 0, v___x_2901_);
v___x_2903_ = v___x_2877_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2904_ = lean_box(0);
lean_inc(v_val_2855_);
v___x_2905_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2894_, v_val_2855_, v___x_2903_);
v___x_2906_ = lean_array_push(v_constOrder_2895_, v_val_2855_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 6, v___x_2906_);
lean_ctor_set(v___x_2897_, 5, v___x_2905_);
v___x_2908_ = v___x_2897_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_stream_2889_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_nameMap_2890_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_levelMap_2891_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_exprMap_2892_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_recursorRuleMap_2893_);
lean_ctor_set(v_reuseFailAlloc_2915_, 5, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2915_, 6, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2910_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v___x_2908_);
lean_ctor_set(v___x_2887_, 0, v___x_2904_);
v___x_2910_ = v___x_2887_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2912_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2910_);
v___x_2912_ = v___x_2882_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_del_object(v___x_2897_);
lean_dec_ref(v_constOrder_2895_);
lean_dec_ref(v_constMap_2894_);
lean_dec_ref(v_recursorRuleMap_2893_);
lean_dec_ref(v_exprMap_2892_);
lean_dec_ref(v_levelMap_2891_);
lean_dec_ref(v_nameMap_2890_);
lean_dec_ref(v_stream_2889_);
lean_del_object(v___x_2887_);
lean_dec(v_fst_2885_);
lean_dec(v_val_2875_);
lean_dec(v_val_2870_);
lean_dec(v_fst_2867_);
v___x_2917_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2918_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2855_, v___x_2899_);
v___x_2919_ = lean_string_append(v___x_2917_, v___x_2918_);
lean_dec_ref(v___x_2918_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 18);
lean_ctor_set(v___x_2877_, 0, v___x_2919_);
v___x_2921_ = v___x_2877_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2923_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2921_);
v___x_2923_ = v___x_2882_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_del_object(v___x_2877_);
lean_dec(v_val_2875_);
lean_dec(v_val_2870_);
lean_dec(v_fst_2867_);
lean_dec(v_val_2855_);
v_a_2929_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2879_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2879_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v___x_2874_);
lean_dec(v_val_2870_);
lean_dec(v_fst_2867_);
lean_dec(v_snd_2866_);
lean_dec(v_val_2855_);
lean_dec_ref(v_elems_2848_);
v___x_2938_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2939_ = l_Nat_reprFast(v_a_2860_);
v___x_2940_ = lean_string_append(v___x_2938_, v___x_2939_);
lean_dec_ref(v___x_2939_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 18);
lean_ctor_set(v___x_2872_, 0, v___x_2940_);
v___x_2942_ = v___x_2872_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2944_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set_tag(v___x_2864_, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2942_);
v___x_2944_ = v___x_2864_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
lean_dec(v___x_2869_);
lean_dec(v_fst_2867_);
lean_dec(v_snd_2866_);
lean_dec(v_a_2860_);
lean_dec(v_val_2855_);
lean_dec_ref(v_elems_2848_);
v___x_2948_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2949_ = l_Nat_reprFast(v_a_2859_);
v___x_2950_ = lean_string_append(v___x_2948_, v___x_2949_);
lean_dec_ref(v___x_2949_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 18);
lean_ctor_set(v___x_2857_, 0, v___x_2950_);
v___x_2952_ = v___x_2857_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set_tag(v___x_2864_, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2952_);
v___x_2954_ = v___x_2864_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_a_2860_);
lean_dec(v_a_2859_);
lean_del_object(v___x_2857_);
lean_dec(v_val_2855_);
lean_dec_ref(v_elems_2848_);
v_a_2958_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2861_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2861_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec(v___x_2854_);
lean_dec_ref(v_elems_2848_);
lean_dec(v_mantissa_2838_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec_ref(v_a_2795_);
v___x_2967_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2968_ = l_Nat_reprFast(v_a_2853_);
v___x_2969_ = lean_string_append(v___x_2967_, v___x_2968_);
lean_dec_ref(v___x_2968_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set_tag(v___x_2850_, 18);
lean_ctor_set(v___x_2850_, 0, v___x_2969_);
v___x_2971_ = v___x_2850_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2971_);
v___x_2973_ = v___x_2846_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
else
{
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec(v_mantissa_2838_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2809_;
}
}
}
else
{
lean_dec(v___x_2843_);
lean_dec(v_mantissa_2838_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2809_;
}
}
}
else
{
lean_dec(v_exponent_2839_);
lean_dec(v_mantissa_2838_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2806_;
}
}
else
{
lean_dec(v_val_2836_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2806_;
}
}
else
{
lean_dec(v___x_2835_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2806_;
}
}
}
else
{
lean_dec(v_exponent_2831_);
lean_dec(v_mantissa_2830_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2803_;
}
}
else
{
lean_dec(v_val_2828_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2803_;
}
}
else
{
lean_dec(v___x_2827_);
lean_dec_ref(v_elems_2825_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2803_;
}
}
else
{
lean_dec(v_val_2824_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2800_;
}
}
else
{
lean_dec(v___x_2823_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2800_;
}
}
}
else
{
lean_dec(v_exponent_2817_);
lean_dec(v_mantissa_2816_);
lean_dec_ref(v_a_2795_);
goto v___jp_2797_;
}
}
else
{
lean_dec(v_val_2814_);
lean_dec_ref(v_a_2795_);
goto v___jp_2797_;
}
}
else
{
lean_dec(v___x_2813_);
lean_dec_ref(v_a_2795_);
goto v___jp_2797_;
}
v___jp_2797_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
v___jp_2800_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
v___jp_2803_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
v___jp_2806_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
v___jp_2809_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
return v___x_2811_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_2794_ = stack[0].m_obj;
lean_object* v_a_2795_ = stack[1].m_obj;
lean_object* v_res_2978_;
v_res_2978_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_data_2794_, v_a_2795_);
stack->m_obj
 = v_res_2978_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___boxed(lean_object* v_data_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_data_2979_, v_a_2980_);
lean_dec(v_data_2979_);
return v_res_2982_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(lean_object* v_data_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 1)
{
lean_object* v_val_3006_; 
v_val_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_val_3006_);
lean_dec_ref_known(v___x_3005_, 1);
if (lean_obj_tag(v_val_3006_) == 2)
{
lean_object* v_n_3007_; lean_object* v_mantissa_3008_; lean_object* v_exponent_3009_; lean_object* v_natZero_3010_; lean_object* v_intZero_3011_; uint8_t v_isNeg_3012_; 
v_n_3007_ = lean_ctor_get(v_val_3006_, 0);
lean_inc_ref(v_n_3007_);
lean_dec_ref_known(v_val_3006_, 1);
v_mantissa_3008_ = lean_ctor_get(v_n_3007_, 0);
lean_inc(v_mantissa_3008_);
v_exponent_3009_ = lean_ctor_get(v_n_3007_, 1);
lean_inc(v_exponent_3009_);
lean_dec_ref(v_n_3007_);
v_natZero_3010_ = lean_unsigned_to_nat(0u);
v_intZero_3011_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3012_ = lean_int_dec_lt(v_mantissa_3008_, v_intZero_3011_);
if (v_isNeg_3012_ == 0)
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_nat_dec_eq(v_exponent_3009_, v_natZero_3010_);
lean_dec(v_exponent_3009_);
if (v___x_3013_ == 0)
{
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_3001_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 1)
{
lean_object* v_val_3016_; 
v_val_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v___x_3015_, 1);
if (lean_obj_tag(v_val_3016_) == 4)
{
lean_object* v_elems_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_elems_3017_ = lean_ctor_get(v_val_3016_, 0);
lean_inc_ref(v_elems_3017_);
lean_dec_ref_known(v_val_3016_, 1);
v___x_3018_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 1);
if (lean_obj_tag(v_val_3020_) == 2)
{
lean_object* v_n_3021_; lean_object* v_mantissa_3022_; lean_object* v_exponent_3023_; uint8_t v_isNeg_3024_; 
v_n_3021_ = lean_ctor_get(v_val_3020_, 0);
lean_inc_ref(v_n_3021_);
lean_dec_ref_known(v_val_3020_, 1);
v_mantissa_3022_ = lean_ctor_get(v_n_3021_, 0);
lean_inc(v_mantissa_3022_);
v_exponent_3023_ = lean_ctor_get(v_n_3021_, 1);
lean_inc(v_exponent_3023_);
lean_dec_ref(v_n_3021_);
v_isNeg_3024_ = lean_int_dec_lt(v_mantissa_3022_, v_intZero_3011_);
if (v_isNeg_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_nat_dec_eq(v_exponent_3023_, v_natZero_3010_);
lean_dec(v_exponent_3023_);
if (v___x_3025_ == 0)
{
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2995_;
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_3027_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 1)
{
lean_object* v_val_3028_; 
v_val_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___x_3027_, 1);
if (lean_obj_tag(v_val_3028_) == 2)
{
lean_object* v_n_3029_; lean_object* v_mantissa_3030_; lean_object* v_exponent_3031_; uint8_t v_isNeg_3032_; 
v_n_3029_ = lean_ctor_get(v_val_3028_, 0);
lean_inc_ref(v_n_3029_);
lean_dec_ref_known(v_val_3028_, 1);
v_mantissa_3030_ = lean_ctor_get(v_n_3029_, 0);
lean_inc(v_mantissa_3030_);
v_exponent_3031_ = lean_ctor_get(v_n_3029_, 1);
lean_inc(v_exponent_3031_);
lean_dec_ref(v_n_3029_);
v_isNeg_3032_ = lean_int_dec_lt(v_mantissa_3030_, v_intZero_3011_);
if (v_isNeg_3032_ == 0)
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_eq(v_exponent_3031_, v_natZero_3010_);
lean_dec(v_exponent_3031_);
if (v___x_3033_ == 0)
{
lean_dec(v_mantissa_3030_);
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2992_;
}
else
{
lean_object* v_a_3034_; lean_object* v_a_3035_; lean_object* v_a_3036_; uint8_t v_b_3038_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_a_3034_ = lean_nat_abs(v_mantissa_3008_);
lean_dec(v_mantissa_3008_);
v_a_3035_ = lean_nat_abs(v_mantissa_3022_);
lean_dec(v_mantissa_3022_);
v_a_3036_ = lean_nat_abs(v_mantissa_3030_);
lean_dec(v_mantissa_3030_);
v___x_3172_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3172_);
if (lean_obj_tag(v___x_3173_) == 0)
{
v_b_3038_ = v_isNeg_3032_;
goto v___jp_3037_;
}
else
{
lean_object* v_val_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3183_; 
v_val_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_val_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
if (lean_obj_tag(v_val_3174_) == 1)
{
uint8_t v_b_3178_; 
lean_del_object(v___x_3176_);
v_b_3178_ = lean_ctor_get_uint8(v_val_3174_, 0);
lean_dec_ref_known(v_val_3174_, 0);
v_b_3038_ = v_b_3178_;
goto v___jp_3037_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_dec(v_val_3174_);
lean_dec(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_elems_3017_);
lean_dec_ref(v_a_2987_);
v___x_3179_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3179_);
v___x_3181_ = v___x_3176_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
v___jp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3040_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2986_, v___x_3039_);
if (lean_obj_tag(v___x_3040_) == 1)
{
lean_object* v_val_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3171_; 
v_val_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3171_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_val_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3171_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
if (lean_obj_tag(v_val_3041_) == 4)
{
lean_object* v_elems_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3170_; 
v_elems_3045_ = lean_ctor_get(v_val_3041_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_val_3041_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3047_ = v_val_3041_;
v_isShared_3048_ = v_isSharedCheck_3170_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_elems_3045_);
lean_dec(v_val_3041_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3170_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_nameMap_3049_; lean_object* v___x_3050_; 
v_nameMap_3049_ = lean_ctor_get(v_a_2987_, 1);
v___x_3050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3049_, v_a_3034_);
if (lean_obj_tag(v___x_3050_) == 1)
{
lean_object* v_val_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3160_; 
lean_del_object(v___x_3047_);
lean_del_object(v___x_3043_);
lean_dec(v_a_3034_);
v_val_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3160_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_val_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3160_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3017_, v_a_2987_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3151_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3151_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3151_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_snd_3060_; lean_object* v_fst_3061_; lean_object* v_exprMap_3062_; lean_object* v___x_3063_; 
v_snd_3060_ = lean_ctor_get(v_a_3056_, 1);
lean_inc(v_snd_3060_);
v_fst_3061_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_fst_3061_);
lean_dec(v_a_3056_);
v_exprMap_3062_ = lean_ctor_get(v_snd_3060_, 3);
v___x_3063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3062_, v_a_3035_);
if (lean_obj_tag(v___x_3063_) == 1)
{
lean_object* v_val_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3141_; 
lean_del_object(v___x_3053_);
lean_dec(v_a_3035_);
v_val_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3141_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_val_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3141_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3062_, v_a_3036_);
if (lean_obj_tag(v___x_3068_) == 1)
{
lean_object* v_val_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3131_; 
lean_del_object(v___x_3066_);
lean_del_object(v___x_3058_);
lean_dec(v_a_3036_);
v_val_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3131_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_val_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3131_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3045_, v_snd_3060_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3122_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3122_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3122_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v_snd_3078_; lean_object* v_fst_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3121_; 
v_snd_3078_ = lean_ctor_get(v_a_3074_, 1);
v_fst_3079_ = lean_ctor_get(v_a_3074_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_a_3074_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3081_ = v_a_3074_;
v_isShared_3082_ = v_isSharedCheck_3121_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_snd_3078_);
lean_inc(v_fst_3079_);
lean_dec(v_a_3074_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3121_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v_stream_3083_; lean_object* v_nameMap_3084_; lean_object* v_levelMap_3085_; lean_object* v_exprMap_3086_; lean_object* v_recursorRuleMap_3087_; lean_object* v_constMap_3088_; lean_object* v_constOrder_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3120_; 
v_stream_3083_ = lean_ctor_get(v_snd_3078_, 0);
v_nameMap_3084_ = lean_ctor_get(v_snd_3078_, 1);
v_levelMap_3085_ = lean_ctor_get(v_snd_3078_, 2);
v_exprMap_3086_ = lean_ctor_get(v_snd_3078_, 3);
v_recursorRuleMap_3087_ = lean_ctor_get(v_snd_3078_, 4);
v_constMap_3088_ = lean_ctor_get(v_snd_3078_, 5);
v_constOrder_3089_ = lean_ctor_get(v_snd_3078_, 6);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_snd_3078_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3091_ = v_snd_3078_;
v_isShared_3092_ = v_isSharedCheck_3120_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_constOrder_3089_);
lean_inc(v_constMap_3088_);
lean_inc(v_recursorRuleMap_3087_);
lean_inc(v_exprMap_3086_);
lean_inc(v_levelMap_3085_);
lean_inc(v_nameMap_3084_);
lean_inc(v_stream_3083_);
lean_dec(v_snd_3078_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3120_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
uint8_t v___x_3093_; 
v___x_3093_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3088_, v_val_3051_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
lean_inc(v_val_3051_);
v___x_3094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3094_, 0, v_val_3051_);
lean_ctor_set(v___x_3094_, 1, v_fst_3061_);
lean_ctor_set(v___x_3094_, 2, v_val_3064_);
v___x_3095_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_val_3069_);
lean_ctor_set(v___x_3095_, 2, v_fst_3079_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3, v_b_3038_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 3);
lean_ctor_set(v___x_3071_, 0, v___x_3095_);
v___x_3097_ = v___x_3071_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3098_ = lean_box(0);
lean_inc(v_val_3051_);
v___x_3099_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3088_, v_val_3051_, v___x_3097_);
v___x_3100_ = lean_array_push(v_constOrder_3089_, v_val_3051_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 6, v___x_3100_);
lean_ctor_set(v___x_3091_, 5, v___x_3099_);
v___x_3102_ = v___x_3091_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_stream_3083_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_nameMap_3084_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_levelMap_3085_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_exprMap_3086_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_recursorRuleMap_3087_);
lean_ctor_set(v_reuseFailAlloc_3109_, 5, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3109_, 6, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3102_);
lean_ctor_set(v___x_3081_, 0, v___x_3098_);
v___x_3104_ = v___x_3081_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3106_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3104_);
v___x_3106_ = v___x_3076_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_del_object(v___x_3091_);
lean_dec_ref(v_constOrder_3089_);
lean_dec_ref(v_constMap_3088_);
lean_dec_ref(v_recursorRuleMap_3087_);
lean_dec_ref(v_exprMap_3086_);
lean_dec_ref(v_levelMap_3085_);
lean_dec_ref(v_nameMap_3084_);
lean_dec_ref(v_stream_3083_);
lean_del_object(v___x_3081_);
lean_dec(v_fst_3079_);
lean_dec(v_val_3069_);
lean_dec(v_val_3064_);
lean_dec(v_fst_3061_);
v___x_3111_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3112_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3051_, v___x_3093_);
v___x_3113_ = lean_string_append(v___x_3111_, v___x_3112_);
lean_dec_ref(v___x_3112_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 18);
lean_ctor_set(v___x_3071_, 0, v___x_3113_);
v___x_3115_ = v___x_3071_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 1);
lean_ctor_set(v___x_3076_, 0, v___x_3115_);
v___x_3117_ = v___x_3076_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_del_object(v___x_3071_);
lean_dec(v_val_3069_);
lean_dec(v_val_3064_);
lean_dec(v_fst_3061_);
lean_dec(v_val_3051_);
v_a_3123_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3073_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3073_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v___x_3068_);
lean_dec(v_val_3064_);
lean_dec(v_fst_3061_);
lean_dec(v_snd_3060_);
lean_dec(v_val_3051_);
lean_dec_ref(v_elems_3045_);
v___x_3132_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3133_ = l_Nat_reprFast(v_a_3036_);
v___x_3134_ = lean_string_append(v___x_3132_, v___x_3133_);
lean_dec_ref(v___x_3133_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 18);
lean_ctor_set(v___x_3066_, 0, v___x_3134_);
v___x_3136_ = v___x_3066_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 1);
lean_ctor_set(v___x_3058_, 0, v___x_3136_);
v___x_3138_ = v___x_3058_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
lean_dec(v___x_3063_);
lean_dec(v_fst_3061_);
lean_dec(v_snd_3060_);
lean_dec(v_val_3051_);
lean_dec_ref(v_elems_3045_);
lean_dec(v_a_3036_);
v___x_3142_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3143_ = l_Nat_reprFast(v_a_3035_);
v___x_3144_ = lean_string_append(v___x_3142_, v___x_3143_);
lean_dec_ref(v___x_3143_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 18);
lean_ctor_set(v___x_3053_, 0, v___x_3144_);
v___x_3146_ = v___x_3053_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3148_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 1);
lean_ctor_set(v___x_3058_, 0, v___x_3146_);
v___x_3148_ = v___x_3058_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_del_object(v___x_3053_);
lean_dec(v_val_3051_);
lean_dec_ref(v_elems_3045_);
lean_dec(v_a_3036_);
lean_dec(v_a_3035_);
v_a_3152_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3055_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3055_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_dec(v___x_3050_);
lean_dec_ref(v_elems_3045_);
lean_dec(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_elems_3017_);
lean_dec_ref(v_a_2987_);
v___x_3161_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3162_ = l_Nat_reprFast(v_a_3034_);
v___x_3163_ = lean_string_append(v___x_3161_, v___x_3162_);
lean_dec_ref(v___x_3162_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set_tag(v___x_3047_, 18);
lean_ctor_set(v___x_3047_, 0, v___x_3163_);
v___x_3165_ = v___x_3047_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3165_);
v___x_3167_ = v___x_3043_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
else
{
lean_del_object(v___x_3043_);
lean_dec(v_val_3041_);
lean_dec(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_elems_3017_);
lean_dec_ref(v_a_2987_);
goto v___jp_2989_;
}
}
}
else
{
lean_dec(v___x_3040_);
lean_dec(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_elems_3017_);
lean_dec_ref(v_a_2987_);
goto v___jp_2989_;
}
}
}
}
else
{
lean_dec(v_exponent_3031_);
lean_dec(v_mantissa_3030_);
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2992_;
}
}
else
{
lean_dec(v_val_3028_);
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2992_;
}
}
else
{
lean_dec(v___x_3027_);
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2992_;
}
}
}
else
{
lean_dec(v_exponent_3023_);
lean_dec(v_mantissa_3022_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2995_;
}
}
else
{
lean_dec(v_val_3020_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2995_;
}
}
else
{
lean_dec(v___x_3019_);
lean_dec_ref(v_elems_3017_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2995_;
}
}
else
{
lean_dec(v_val_3016_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2998_;
}
}
else
{
lean_dec(v___x_3015_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_2998_;
}
}
}
else
{
lean_dec(v_exponent_3009_);
lean_dec(v_mantissa_3008_);
lean_dec_ref(v_a_2987_);
goto v___jp_3001_;
}
}
else
{
lean_dec(v_val_3006_);
lean_dec_ref(v_a_2987_);
goto v___jp_3001_;
}
}
else
{
lean_dec(v___x_3005_);
lean_dec_ref(v_a_2987_);
goto v___jp_3001_;
}
v___jp_2989_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
v___jp_2992_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
v___jp_2995_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
v___jp_2998_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
v___jp_3001_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_2986_ = stack[0].m_obj;
lean_object* v_a_2987_ = stack[1].m_obj;
lean_object* v_res_3184_;
v_res_3184_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_data_2986_, v_a_2987_);
stack->m_obj
 = v_res_3184_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___boxed(lean_object* v_data_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_data_3185_, v_a_3186_);
lean_dec(v_data_3185_);
return v_res_3188_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(lean_object* v_data_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3197_, v___x_3212_);
if (lean_obj_tag(v___x_3213_) == 1)
{
lean_object* v_val_3214_; 
v_val_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_val_3214_);
lean_dec_ref_known(v___x_3213_, 1);
if (lean_obj_tag(v_val_3214_) == 2)
{
lean_object* v_n_3215_; lean_object* v_mantissa_3216_; lean_object* v_exponent_3217_; lean_object* v_natZero_3218_; lean_object* v_intZero_3219_; uint8_t v_isNeg_3220_; 
v_n_3215_ = lean_ctor_get(v_val_3214_, 0);
lean_inc_ref(v_n_3215_);
lean_dec_ref_known(v_val_3214_, 1);
v_mantissa_3216_ = lean_ctor_get(v_n_3215_, 0);
lean_inc(v_mantissa_3216_);
v_exponent_3217_ = lean_ctor_get(v_n_3215_, 1);
lean_inc(v_exponent_3217_);
lean_dec_ref(v_n_3215_);
v_natZero_3218_ = lean_unsigned_to_nat(0u);
v_intZero_3219_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3220_ = lean_int_dec_lt(v_mantissa_3216_, v_intZero_3219_);
if (v_isNeg_3220_ == 0)
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_nat_dec_eq(v_exponent_3217_, v_natZero_3218_);
lean_dec(v_exponent_3217_);
if (v___x_3221_ == 0)
{
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3209_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3197_, v___x_3222_);
if (lean_obj_tag(v___x_3223_) == 1)
{
lean_object* v_val_3224_; 
v_val_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v___x_3223_, 1);
if (lean_obj_tag(v_val_3224_) == 4)
{
lean_object* v_elems_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_elems_3225_ = lean_ctor_get(v_val_3224_, 0);
lean_inc_ref(v_elems_3225_);
lean_dec_ref_known(v_val_3224_, 1);
v___x_3226_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3197_, v___x_3226_);
if (lean_obj_tag(v___x_3227_) == 1)
{
lean_object* v_val_3228_; 
v_val_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_val_3228_);
lean_dec_ref_known(v___x_3227_, 1);
if (lean_obj_tag(v_val_3228_) == 2)
{
lean_object* v_n_3229_; lean_object* v_mantissa_3230_; lean_object* v_exponent_3231_; uint8_t v_isNeg_3232_; 
v_n_3229_ = lean_ctor_get(v_val_3228_, 0);
lean_inc_ref(v_n_3229_);
lean_dec_ref_known(v_val_3228_, 1);
v_mantissa_3230_ = lean_ctor_get(v_n_3229_, 0);
lean_inc(v_mantissa_3230_);
v_exponent_3231_ = lean_ctor_get(v_n_3229_, 1);
lean_inc(v_exponent_3231_);
lean_dec_ref(v_n_3229_);
v_isNeg_3232_ = lean_int_dec_lt(v_mantissa_3230_, v_intZero_3219_);
if (v_isNeg_3232_ == 0)
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_nat_dec_eq(v_exponent_3231_, v_natZero_3218_);
lean_dec(v_exponent_3231_);
if (v___x_3233_ == 0)
{
lean_dec(v_mantissa_3230_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3203_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2));
v___x_3235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3197_, v___x_3234_);
if (lean_obj_tag(v___x_3235_) == 1)
{
lean_object* v_val_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3364_; 
v_val_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3364_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_val_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3364_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
if (lean_obj_tag(v_val_3236_) == 3)
{
lean_object* v_s_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3363_; 
v_s_3240_ = lean_ctor_get(v_val_3236_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_val_3236_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3242_ = v_val_3236_;
v_isShared_3243_ = v_isSharedCheck_3363_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_s_3240_);
lean_dec(v_val_3236_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3363_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_nameMap_3244_; lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_nameMap_3244_ = lean_ctor_get(v_a_3198_, 1);
v_a_3245_ = lean_nat_abs(v_mantissa_3216_);
lean_dec(v_mantissa_3216_);
v___x_3246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3246_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_a_3245_);
lean_del_object(v___x_3238_);
v_val_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3353_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_val_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3353_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v_a_3251_; lean_object* v___x_3252_; 
v_a_3251_ = lean_nat_abs(v_mantissa_3230_);
lean_dec(v_mantissa_3230_);
v___x_3252_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3225_, v_a_3198_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3344_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3344_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3344_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_snd_3257_; lean_object* v_fst_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3343_; 
v_snd_3257_ = lean_ctor_get(v_a_3253_, 1);
v_fst_3258_ = lean_ctor_get(v_a_3253_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_a_3253_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3260_ = v_a_3253_;
v_isShared_3261_ = v_isSharedCheck_3343_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_snd_3257_);
lean_inc(v_fst_3258_);
lean_dec(v_a_3253_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3343_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_stream_3262_; lean_object* v_nameMap_3263_; lean_object* v_levelMap_3264_; lean_object* v_exprMap_3265_; lean_object* v_recursorRuleMap_3266_; lean_object* v_constMap_3267_; lean_object* v_constOrder_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3342_; 
v_stream_3262_ = lean_ctor_get(v_snd_3257_, 0);
v_nameMap_3263_ = lean_ctor_get(v_snd_3257_, 1);
v_levelMap_3264_ = lean_ctor_get(v_snd_3257_, 2);
v_exprMap_3265_ = lean_ctor_get(v_snd_3257_, 3);
v_recursorRuleMap_3266_ = lean_ctor_get(v_snd_3257_, 4);
v_constMap_3267_ = lean_ctor_get(v_snd_3257_, 5);
v_constOrder_3268_ = lean_ctor_get(v_snd_3257_, 6);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_snd_3257_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3270_ = v_snd_3257_;
v_isShared_3271_ = v_isSharedCheck_3342_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_constOrder_3268_);
lean_inc(v_constMap_3267_);
lean_inc(v_recursorRuleMap_3266_);
lean_inc(v_exprMap_3265_);
lean_inc(v_levelMap_3264_);
lean_inc(v_nameMap_3263_);
lean_inc(v_stream_3262_);
lean_dec(v_snd_3257_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3342_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3265_, v_a_3251_);
if (lean_obj_tag(v___x_3272_) == 1)
{
lean_object* v_val_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_a_3251_);
v_val_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3332_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_val_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3332_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
uint8_t v_kind_3278_; lean_object* v_stream_3279_; lean_object* v_nameMap_3280_; lean_object* v_levelMap_3281_; lean_object* v_exprMap_3282_; lean_object* v_recursorRuleMap_3283_; lean_object* v_constMap_3284_; lean_object* v_constOrder_3285_; uint8_t v___x_3313_; 
v___x_3313_ = lean_string_dec_eq(v_s_3240_, v___x_3226_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3315_ = lean_string_dec_eq(v_s_3240_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4));
v___x_3317_ = lean_string_dec_eq(v_s_3240_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5));
v___x_3319_ = lean_string_dec_eq(v_s_3240_, v___x_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_del_object(v___x_3275_);
lean_dec(v_val_3273_);
lean_del_object(v___x_3270_);
lean_dec_ref(v_constOrder_3268_);
lean_dec_ref(v_constMap_3267_);
lean_dec_ref(v_recursorRuleMap_3266_);
lean_dec_ref(v_exprMap_3265_);
lean_dec_ref(v_levelMap_3264_);
lean_dec_ref(v_nameMap_3263_);
lean_dec_ref(v_stream_3262_);
lean_del_object(v___x_3260_);
lean_dec(v_fst_3258_);
lean_del_object(v___x_3255_);
lean_dec(v_val_3247_);
v___x_3320_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6));
v___x_3321_ = lean_string_append(v___x_3320_, v_s_3240_);
lean_dec_ref(v_s_3240_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 18);
lean_ctor_set(v___x_3249_, 0, v___x_3321_);
v___x_3323_ = v___x_3249_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3325_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 1);
lean_ctor_set(v___x_3242_, 0, v___x_3323_);
v___x_3325_ = v___x_3242_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
else
{
uint8_t v___x_3328_; 
lean_del_object(v___x_3249_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v___x_3328_ = 3;
v_kind_3278_ = v___x_3328_;
v_stream_3279_ = v_stream_3262_;
v_nameMap_3280_ = v_nameMap_3263_;
v_levelMap_3281_ = v_levelMap_3264_;
v_exprMap_3282_ = v_exprMap_3265_;
v_recursorRuleMap_3283_ = v_recursorRuleMap_3266_;
v_constMap_3284_ = v_constMap_3267_;
v_constOrder_3285_ = v_constOrder_3268_;
goto v___jp_3277_;
}
}
else
{
uint8_t v___x_3329_; 
lean_del_object(v___x_3249_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v___x_3329_ = 2;
v_kind_3278_ = v___x_3329_;
v_stream_3279_ = v_stream_3262_;
v_nameMap_3280_ = v_nameMap_3263_;
v_levelMap_3281_ = v_levelMap_3264_;
v_exprMap_3282_ = v_exprMap_3265_;
v_recursorRuleMap_3283_ = v_recursorRuleMap_3266_;
v_constMap_3284_ = v_constMap_3267_;
v_constOrder_3285_ = v_constOrder_3268_;
goto v___jp_3277_;
}
}
else
{
uint8_t v___x_3330_; 
lean_del_object(v___x_3249_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v___x_3330_ = 1;
v_kind_3278_ = v___x_3330_;
v_stream_3279_ = v_stream_3262_;
v_nameMap_3280_ = v_nameMap_3263_;
v_levelMap_3281_ = v_levelMap_3264_;
v_exprMap_3282_ = v_exprMap_3265_;
v_recursorRuleMap_3283_ = v_recursorRuleMap_3266_;
v_constMap_3284_ = v_constMap_3267_;
v_constOrder_3285_ = v_constOrder_3268_;
goto v___jp_3277_;
}
}
else
{
uint8_t v___x_3331_; 
lean_del_object(v___x_3249_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v___x_3331_ = 0;
v_kind_3278_ = v___x_3331_;
v_stream_3279_ = v_stream_3262_;
v_nameMap_3280_ = v_nameMap_3263_;
v_levelMap_3281_ = v_levelMap_3264_;
v_exprMap_3282_ = v_exprMap_3265_;
v_recursorRuleMap_3283_ = v_recursorRuleMap_3266_;
v_constMap_3284_ = v_constMap_3267_;
v_constOrder_3285_ = v_constOrder_3268_;
goto v___jp_3277_;
}
v___jp_3277_:
{
uint8_t v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3284_, v_val_3247_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
lean_inc(v_val_3247_);
v___x_3287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3287_, 0, v_val_3247_);
lean_ctor_set(v___x_3287_, 1, v_fst_3258_);
lean_ctor_set(v___x_3287_, 2, v_val_3273_);
v___x_3288_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*1, v_kind_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 4);
lean_ctor_set(v___x_3275_, 0, v___x_3288_);
v___x_3290_ = v___x_3275_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3291_ = lean_box(0);
lean_inc(v_val_3247_);
v___x_3292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3284_, v_val_3247_, v___x_3290_);
v___x_3293_ = lean_array_push(v_constOrder_3285_, v_val_3247_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 6, v___x_3293_);
lean_ctor_set(v___x_3270_, 5, v___x_3292_);
lean_ctor_set(v___x_3270_, 4, v_recursorRuleMap_3283_);
lean_ctor_set(v___x_3270_, 3, v_exprMap_3282_);
lean_ctor_set(v___x_3270_, 2, v_levelMap_3281_);
lean_ctor_set(v___x_3270_, 1, v_nameMap_3280_);
lean_ctor_set(v___x_3270_, 0, v_stream_3279_);
v___x_3295_ = v___x_3270_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_stream_3279_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_nameMap_3280_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_levelMap_3281_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_exprMap_3282_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_recursorRuleMap_3283_);
lean_ctor_set(v_reuseFailAlloc_3302_, 5, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3302_, 6, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3295_);
lean_ctor_set(v___x_3260_, 0, v___x_3291_);
v___x_3297_ = v___x_3260_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3297_);
v___x_3299_ = v___x_3255_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_dec_ref(v_constOrder_3285_);
lean_dec_ref(v_constMap_3284_);
lean_dec_ref(v_recursorRuleMap_3283_);
lean_dec_ref(v_exprMap_3282_);
lean_dec_ref(v_levelMap_3281_);
lean_dec_ref(v_nameMap_3280_);
lean_dec_ref(v_stream_3279_);
lean_dec(v_val_3273_);
lean_del_object(v___x_3270_);
lean_del_object(v___x_3260_);
lean_dec(v_fst_3258_);
v___x_3304_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3247_, v___x_3286_);
v___x_3306_ = lean_string_append(v___x_3304_, v___x_3305_);
lean_dec_ref(v___x_3305_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 18);
lean_ctor_set(v___x_3275_, 0, v___x_3306_);
v___x_3308_ = v___x_3275_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3308_);
v___x_3310_ = v___x_3255_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
lean_dec(v___x_3272_);
lean_del_object(v___x_3270_);
lean_dec_ref(v_constOrder_3268_);
lean_dec_ref(v_constMap_3267_);
lean_dec_ref(v_recursorRuleMap_3266_);
lean_dec_ref(v_exprMap_3265_);
lean_dec_ref(v_levelMap_3264_);
lean_dec_ref(v_nameMap_3263_);
lean_dec_ref(v_stream_3262_);
lean_del_object(v___x_3260_);
lean_dec(v_fst_3258_);
lean_dec(v_val_3247_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v___x_3333_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3334_ = l_Nat_reprFast(v_a_3251_);
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
lean_dec_ref(v___x_3334_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 18);
lean_ctor_set(v___x_3249_, 0, v___x_3335_);
v___x_3337_ = v___x_3249_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3337_);
v___x_3339_ = v___x_3255_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3251_);
lean_del_object(v___x_3249_);
lean_dec(v_val_3247_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_s_3240_);
v_a_3345_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3252_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3252_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec(v___x_3246_);
lean_dec_ref(v_s_3240_);
lean_dec(v_mantissa_3230_);
lean_dec_ref(v_elems_3225_);
lean_dec_ref(v_a_3198_);
v___x_3354_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3355_ = l_Nat_reprFast(v_a_3245_);
v___x_3356_ = lean_string_append(v___x_3354_, v___x_3355_);
lean_dec_ref(v___x_3355_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 18);
lean_ctor_set(v___x_3242_, 0, v___x_3356_);
v___x_3358_ = v___x_3242_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3358_);
v___x_3360_ = v___x_3238_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
else
{
lean_del_object(v___x_3238_);
lean_dec(v_val_3236_);
lean_dec(v_mantissa_3230_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3200_;
}
}
}
else
{
lean_dec(v___x_3235_);
lean_dec(v_mantissa_3230_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3200_;
}
}
}
else
{
lean_dec(v_exponent_3231_);
lean_dec(v_mantissa_3230_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3203_;
}
}
else
{
lean_dec(v_val_3228_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3203_;
}
}
else
{
lean_dec(v___x_3227_);
lean_dec_ref(v_elems_3225_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3203_;
}
}
else
{
lean_dec(v_val_3224_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3206_;
}
}
else
{
lean_dec(v___x_3223_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3206_;
}
}
}
else
{
lean_dec(v_exponent_3217_);
lean_dec(v_mantissa_3216_);
lean_dec_ref(v_a_3198_);
goto v___jp_3209_;
}
}
else
{
lean_dec(v_val_3214_);
lean_dec_ref(v_a_3198_);
goto v___jp_3209_;
}
}
else
{
lean_dec(v___x_3213_);
lean_dec_ref(v_a_3198_);
goto v___jp_3209_;
}
v___jp_3200_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
v___jp_3203_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
v___jp_3206_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
v___jp_3209_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_3197_ = stack[0].m_obj;
lean_object* v_a_3198_ = stack[1].m_obj;
lean_object* v_res_3365_;
v_res_3365_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_data_3197_, v_a_3198_);
stack->m_obj
 = v_res_3365_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___boxed(lean_object* v_data_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_data_3366_, v_a_3367_);
lean_dec(v_data_3366_);
return v_res_3369_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(lean_object* v_json_3382_, lean_object* v_a_3383_){
_start:
{
if (lean_obj_tag(v_json_3382_) == 5)
{
lean_object* v_kvPairs_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_kvPairs_3418_ = lean_ctor_get(v_json_3382_, 0);
v___x_3419_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3419_);
if (lean_obj_tag(v___x_3420_) == 1)
{
lean_object* v_val_3421_; 
v_val_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_val_3421_);
lean_dec_ref_known(v___x_3420_, 1);
if (lean_obj_tag(v_val_3421_) == 2)
{
lean_object* v_n_3422_; lean_object* v_mantissa_3423_; lean_object* v_exponent_3424_; lean_object* v_natZero_3425_; lean_object* v_intZero_3426_; uint8_t v_isNeg_3427_; 
v_n_3422_ = lean_ctor_get(v_val_3421_, 0);
lean_inc_ref(v_n_3422_);
lean_dec_ref_known(v_val_3421_, 1);
v_mantissa_3423_ = lean_ctor_get(v_n_3422_, 0);
lean_inc(v_mantissa_3423_);
v_exponent_3424_ = lean_ctor_get(v_n_3422_, 1);
lean_inc(v_exponent_3424_);
lean_dec_ref(v_n_3422_);
v_natZero_3425_ = lean_unsigned_to_nat(0u);
v_intZero_3426_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3427_ = lean_int_dec_lt(v_mantissa_3423_, v_intZero_3426_);
if (v_isNeg_3427_ == 0)
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_eq(v_exponent_3424_, v_natZero_3425_);
lean_dec(v_exponent_3424_);
if (v___x_3428_ == 0)
{
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3385_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3430_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3429_);
if (lean_obj_tag(v___x_3430_) == 1)
{
lean_object* v_val_3431_; 
v_val_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_val_3431_);
lean_dec_ref_known(v___x_3430_, 1);
if (lean_obj_tag(v_val_3431_) == 4)
{
lean_object* v_elems_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_elems_3432_ = lean_ctor_get(v_val_3431_, 0);
lean_inc_ref(v_elems_3432_);
lean_dec_ref_known(v_val_3431_, 1);
v___x_3433_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3433_);
if (lean_obj_tag(v___x_3434_) == 1)
{
lean_object* v_val_3435_; 
v_val_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v___x_3434_, 1);
if (lean_obj_tag(v_val_3435_) == 2)
{
lean_object* v_n_3436_; lean_object* v_mantissa_3437_; lean_object* v_exponent_3438_; uint8_t v_isNeg_3439_; 
v_n_3436_ = lean_ctor_get(v_val_3435_, 0);
lean_inc_ref(v_n_3436_);
lean_dec_ref_known(v_val_3435_, 1);
v_mantissa_3437_ = lean_ctor_get(v_n_3436_, 0);
lean_inc(v_mantissa_3437_);
v_exponent_3438_ = lean_ctor_get(v_n_3436_, 1);
lean_inc(v_exponent_3438_);
lean_dec_ref(v_n_3436_);
v_isNeg_3439_ = lean_int_dec_lt(v_mantissa_3437_, v_intZero_3426_);
if (v_isNeg_3439_ == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_nat_dec_eq(v_exponent_3438_, v_natZero_3425_);
lean_dec(v_exponent_3438_);
if (v___x_3440_ == 0)
{
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3391_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3442_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3441_);
if (lean_obj_tag(v___x_3442_) == 1)
{
lean_object* v_val_3443_; 
v_val_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v___x_3442_, 1);
if (lean_obj_tag(v_val_3443_) == 2)
{
lean_object* v_n_3444_; lean_object* v_mantissa_3445_; lean_object* v_exponent_3446_; uint8_t v_isNeg_3447_; 
v_n_3444_ = lean_ctor_get(v_val_3443_, 0);
lean_inc_ref(v_n_3444_);
lean_dec_ref_known(v_val_3443_, 1);
v_mantissa_3445_ = lean_ctor_get(v_n_3444_, 0);
lean_inc(v_mantissa_3445_);
v_exponent_3446_ = lean_ctor_get(v_n_3444_, 1);
lean_inc(v_exponent_3446_);
lean_dec_ref(v_n_3444_);
v_isNeg_3447_ = lean_int_dec_lt(v_mantissa_3445_, v_intZero_3426_);
if (v_isNeg_3447_ == 0)
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_nat_dec_eq(v_exponent_3446_, v_natZero_3425_);
lean_dec(v_exponent_3446_);
if (v___x_3448_ == 0)
{
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3394_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3449_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_val_3451_; 
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref_known(v___x_3450_, 1);
if (lean_obj_tag(v_val_3451_) == 2)
{
lean_object* v_n_3452_; lean_object* v_mantissa_3453_; lean_object* v_exponent_3454_; uint8_t v_isNeg_3455_; 
v_n_3452_ = lean_ctor_get(v_val_3451_, 0);
lean_inc_ref(v_n_3452_);
lean_dec_ref_known(v_val_3451_, 1);
v_mantissa_3453_ = lean_ctor_get(v_n_3452_, 0);
lean_inc(v_mantissa_3453_);
v_exponent_3454_ = lean_ctor_get(v_n_3452_, 1);
lean_inc(v_exponent_3454_);
lean_dec_ref(v_n_3452_);
v_isNeg_3455_ = lean_int_dec_lt(v_mantissa_3453_, v_intZero_3426_);
if (v_isNeg_3455_ == 0)
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_nat_dec_eq(v_exponent_3454_, v_natZero_3425_);
lean_dec(v_exponent_3454_);
if (v___x_3456_ == 0)
{
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3397_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3457_);
if (lean_obj_tag(v___x_3458_) == 1)
{
lean_object* v_val_3459_; 
v_val_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v___x_3458_, 1);
if (lean_obj_tag(v_val_3459_) == 4)
{
lean_object* v_elems_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_elems_3460_ = lean_ctor_get(v_val_3459_, 0);
lean_inc_ref(v_elems_3460_);
lean_dec_ref_known(v_val_3459_, 1);
v___x_3461_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_3462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3461_);
if (lean_obj_tag(v___x_3462_) == 1)
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3462_, 1);
if (lean_obj_tag(v_val_3463_) == 4)
{
lean_object* v_elems_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_elems_3464_ = lean_ctor_get(v_val_3463_, 0);
lean_inc_ref(v_elems_3464_);
lean_dec_ref_known(v_val_3463_, 1);
v___x_3465_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5));
v___x_3466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3465_);
if (lean_obj_tag(v___x_3466_) == 1)
{
lean_object* v_val_3467_; 
v_val_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v___x_3466_, 1);
if (lean_obj_tag(v_val_3467_) == 2)
{
lean_object* v_n_3468_; lean_object* v_mantissa_3469_; lean_object* v_exponent_3470_; uint8_t v_isNeg_3471_; 
v_n_3468_ = lean_ctor_get(v_val_3467_, 0);
lean_inc_ref(v_n_3468_);
lean_dec_ref_known(v_val_3467_, 1);
v_mantissa_3469_ = lean_ctor_get(v_n_3468_, 0);
lean_inc(v_mantissa_3469_);
v_exponent_3470_ = lean_ctor_get(v_n_3468_, 1);
lean_inc(v_exponent_3470_);
lean_dec_ref(v_n_3468_);
v_isNeg_3471_ = lean_int_dec_lt(v_mantissa_3469_, v_intZero_3426_);
if (v_isNeg_3471_ == 0)
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_nat_dec_eq(v_exponent_3470_, v_natZero_3425_);
lean_dec(v_exponent_3470_);
if (v___x_3472_ == 0)
{
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3406_;
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6));
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3473_);
if (lean_obj_tag(v___x_3474_) == 1)
{
lean_object* v_val_3475_; 
v_val_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v___x_3474_, 1);
if (lean_obj_tag(v_val_3475_) == 1)
{
uint8_t v_b_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_b_3476_ = lean_ctor_get_uint8(v_val_3475_, 0);
lean_dec_ref_known(v_val_3475_, 0);
v___x_3477_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3477_);
if (lean_obj_tag(v___x_3478_) == 1)
{
lean_object* v_val_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3615_; 
v_val_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3615_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_val_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3615_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
if (lean_obj_tag(v_val_3479_) == 1)
{
uint8_t v_b_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_b_3483_ = lean_ctor_get_uint8(v_val_3479_, 0);
lean_dec_ref_known(v_val_3479_, 0);
v___x_3484_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7));
v___x_3485_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3418_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3614_; 
v_val_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3614_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3614_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
if (lean_obj_tag(v_val_3486_) == 1)
{
uint8_t v_b_3490_; lean_object* v_nameMap_3491_; lean_object* v_a_3492_; lean_object* v___x_3493_; 
v_b_3490_ = lean_ctor_get_uint8(v_val_3486_, 0);
lean_dec_ref_known(v_val_3486_, 0);
v_nameMap_3491_ = lean_ctor_get(v_a_3383_, 1);
v_a_3492_ = lean_nat_abs(v_mantissa_3423_);
lean_dec(v_mantissa_3423_);
v___x_3493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3491_, v_a_3492_);
if (lean_obj_tag(v___x_3493_) == 1)
{
lean_object* v_val_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3604_; 
lean_dec(v_a_3492_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3481_);
v_val_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3604_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_val_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3604_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v_a_3498_; lean_object* v_a_3499_; lean_object* v_a_3500_; lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3498_ = lean_nat_abs(v_mantissa_3437_);
lean_dec(v_mantissa_3437_);
v_a_3499_ = lean_nat_abs(v_mantissa_3445_);
lean_dec(v_mantissa_3445_);
v_a_3500_ = lean_nat_abs(v_mantissa_3453_);
lean_dec(v_mantissa_3453_);
v_a_3501_ = lean_nat_abs(v_mantissa_3469_);
lean_dec(v_mantissa_3469_);
v___x_3502_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3432_, v_a_3383_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3595_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3595_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3595_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_snd_3507_; lean_object* v_fst_3508_; lean_object* v_exprMap_3509_; lean_object* v___x_3510_; 
v_snd_3507_ = lean_ctor_get(v_a_3503_, 1);
lean_inc(v_snd_3507_);
v_fst_3508_ = lean_ctor_get(v_a_3503_, 0);
lean_inc(v_fst_3508_);
lean_dec(v_a_3503_);
v_exprMap_3509_ = lean_ctor_get(v_snd_3507_, 3);
v___x_3510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3509_, v_a_3498_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3585_; 
lean_del_object(v___x_3505_);
lean_dec(v_a_3498_);
lean_del_object(v___x_3496_);
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3585_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_val_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3585_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; 
v___x_3515_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3460_, v_snd_3507_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_fst_3517_; lean_object* v_snd_3518_; lean_object* v___x_3519_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v_fst_3517_ = lean_ctor_get(v_a_3516_, 0);
lean_inc(v_fst_3517_);
v_snd_3518_ = lean_ctor_get(v_a_3516_, 1);
lean_inc(v_snd_3518_);
lean_dec(v_a_3516_);
v___x_3519_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3464_, v_snd_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3568_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3568_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3568_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v_snd_3524_; lean_object* v_fst_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3567_; 
v_snd_3524_ = lean_ctor_get(v_a_3520_, 1);
v_fst_3525_ = lean_ctor_get(v_a_3520_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3527_ = v_a_3520_;
v_isShared_3528_ = v_isSharedCheck_3567_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_snd_3524_);
lean_inc(v_fst_3525_);
lean_dec(v_a_3520_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3567_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v_stream_3529_; lean_object* v_nameMap_3530_; lean_object* v_levelMap_3531_; lean_object* v_exprMap_3532_; lean_object* v_recursorRuleMap_3533_; lean_object* v_constMap_3534_; lean_object* v_constOrder_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3566_; 
v_stream_3529_ = lean_ctor_get(v_snd_3524_, 0);
v_nameMap_3530_ = lean_ctor_get(v_snd_3524_, 1);
v_levelMap_3531_ = lean_ctor_get(v_snd_3524_, 2);
v_exprMap_3532_ = lean_ctor_get(v_snd_3524_, 3);
v_recursorRuleMap_3533_ = lean_ctor_get(v_snd_3524_, 4);
v_constMap_3534_ = lean_ctor_get(v_snd_3524_, 5);
v_constOrder_3535_ = lean_ctor_get(v_snd_3524_, 6);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_snd_3524_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3537_ = v_snd_3524_;
v_isShared_3538_ = v_isSharedCheck_3566_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_constOrder_3535_);
lean_inc(v_constMap_3534_);
lean_inc(v_recursorRuleMap_3533_);
lean_inc(v_exprMap_3532_);
lean_inc(v_levelMap_3531_);
lean_inc(v_nameMap_3530_);
lean_inc(v_stream_3529_);
lean_dec(v_snd_3524_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3566_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
uint8_t v___x_3539_; 
v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3534_, v_val_3494_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
lean_inc(v_val_3494_);
v___x_3540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3540_, 0, v_val_3494_);
lean_ctor_set(v___x_3540_, 1, v_fst_3508_);
lean_ctor_set(v___x_3540_, 2, v_val_3511_);
v___x_3541_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v_a_3499_);
lean_ctor_set(v___x_3541_, 2, v_a_3500_);
lean_ctor_set(v___x_3541_, 3, v_fst_3517_);
lean_ctor_set(v___x_3541_, 4, v_fst_3525_);
lean_ctor_set(v___x_3541_, 5, v_a_3501_);
lean_ctor_set_uint8(v___x_3541_, sizeof(void*)*6, v_b_3476_);
lean_ctor_set_uint8(v___x_3541_, sizeof(void*)*6 + 1, v_b_3483_);
lean_ctor_set_uint8(v___x_3541_, sizeof(void*)*6 + 2, v_b_3490_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 5);
lean_ctor_set(v___x_3513_, 0, v___x_3541_);
v___x_3543_ = v___x_3513_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3544_ = lean_box(0);
lean_inc(v_val_3494_);
v___x_3545_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3534_, v_val_3494_, v___x_3543_);
v___x_3546_ = lean_array_push(v_constOrder_3535_, v_val_3494_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 6, v___x_3546_);
lean_ctor_set(v___x_3537_, 5, v___x_3545_);
v___x_3548_ = v___x_3537_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_stream_3529_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_nameMap_3530_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_levelMap_3531_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_exprMap_3532_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_recursorRuleMap_3533_);
lean_ctor_set(v_reuseFailAlloc_3555_, 5, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3555_, 6, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v___x_3548_);
lean_ctor_set(v___x_3527_, 0, v___x_3544_);
v___x_3550_ = v___x_3527_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3550_);
v___x_3552_ = v___x_3522_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_del_object(v___x_3537_);
lean_dec_ref(v_constOrder_3535_);
lean_dec_ref(v_constMap_3534_);
lean_dec_ref(v_recursorRuleMap_3533_);
lean_dec_ref(v_exprMap_3532_);
lean_dec_ref(v_levelMap_3531_);
lean_dec_ref(v_nameMap_3530_);
lean_dec_ref(v_stream_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_fst_3525_);
lean_dec(v_fst_3517_);
lean_dec(v_val_3511_);
lean_dec(v_fst_3508_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
v___x_3557_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3494_, v___x_3539_);
v___x_3559_ = lean_string_append(v___x_3557_, v___x_3558_);
lean_dec_ref(v___x_3558_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 18);
lean_ctor_set(v___x_3513_, 0, v___x_3559_);
v___x_3561_ = v___x_3513_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 1);
lean_ctor_set(v___x_3522_, 0, v___x_3561_);
v___x_3563_ = v___x_3522_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_fst_3517_);
lean_del_object(v___x_3513_);
lean_dec(v_val_3511_);
lean_dec(v_fst_3508_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec(v_val_3494_);
v_a_3569_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3519_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3519_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3513_);
lean_dec(v_val_3511_);
lean_dec(v_fst_3508_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec(v_val_3494_);
lean_dec_ref(v_elems_3464_);
v_a_3577_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3515_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3515_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
lean_dec(v___x_3510_);
lean_dec(v_fst_3508_);
lean_dec(v_snd_3507_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec(v_val_3494_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
v___x_3586_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3587_ = l_Nat_reprFast(v_a_3498_);
v___x_3588_ = lean_string_append(v___x_3586_, v___x_3587_);
lean_dec_ref(v___x_3587_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 18);
lean_ctor_set(v___x_3496_, 0, v___x_3588_);
v___x_3590_ = v___x_3496_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set_tag(v___x_3505_, 1);
lean_ctor_set(v___x_3505_, 0, v___x_3590_);
v___x_3592_ = v___x_3505_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec(v_a_3498_);
lean_del_object(v___x_3496_);
lean_dec(v_val_3494_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
v_a_3596_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3502_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3502_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_dec(v___x_3493_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec_ref(v_a_3383_);
v___x_3605_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3606_ = l_Nat_reprFast(v_a_3492_);
v___x_3607_ = lean_string_append(v___x_3605_, v___x_3606_);
lean_dec_ref(v___x_3606_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set_tag(v___x_3488_, 18);
lean_ctor_set(v___x_3488_, 0, v___x_3607_);
v___x_3609_ = v___x_3488_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3611_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3609_);
v___x_3611_ = v___x_3481_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_del_object(v___x_3488_);
lean_dec(v_val_3486_);
lean_del_object(v___x_3481_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3415_;
}
}
}
else
{
lean_dec(v___x_3485_);
lean_del_object(v___x_3481_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3415_;
}
}
else
{
lean_del_object(v___x_3481_);
lean_dec(v_val_3479_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3412_;
}
}
}
else
{
lean_dec(v___x_3478_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3412_;
}
}
else
{
lean_dec(v_val_3475_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3409_;
}
}
else
{
lean_dec(v___x_3474_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3409_;
}
}
}
else
{
lean_dec(v_exponent_3470_);
lean_dec(v_mantissa_3469_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3406_;
}
}
else
{
lean_dec(v_val_3467_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3406_;
}
}
else
{
lean_dec(v___x_3466_);
lean_dec_ref(v_elems_3464_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3406_;
}
}
else
{
lean_dec(v_val_3463_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3403_;
}
}
else
{
lean_dec(v___x_3462_);
lean_dec_ref(v_elems_3460_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3403_;
}
}
else
{
lean_dec(v_val_3459_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3400_;
}
}
else
{
lean_dec(v___x_3458_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3400_;
}
}
}
else
{
lean_dec(v_exponent_3454_);
lean_dec(v_mantissa_3453_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3397_;
}
}
else
{
lean_dec(v_val_3451_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3397_;
}
}
else
{
lean_dec(v___x_3450_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3397_;
}
}
}
else
{
lean_dec(v_exponent_3446_);
lean_dec(v_mantissa_3445_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3394_;
}
}
else
{
lean_dec(v_val_3443_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3394_;
}
}
else
{
lean_dec(v___x_3442_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3394_;
}
}
}
else
{
lean_dec(v_exponent_3438_);
lean_dec(v_mantissa_3437_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3391_;
}
}
else
{
lean_dec(v_val_3435_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3391_;
}
}
else
{
lean_dec(v___x_3434_);
lean_dec_ref(v_elems_3432_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3391_;
}
}
else
{
lean_dec(v_val_3431_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3388_;
}
}
else
{
lean_dec(v___x_3430_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3388_;
}
}
}
else
{
lean_dec(v_exponent_3424_);
lean_dec(v_mantissa_3423_);
lean_dec_ref(v_a_3383_);
goto v___jp_3385_;
}
}
else
{
lean_dec(v_val_3421_);
lean_dec_ref(v_a_3383_);
goto v___jp_3385_;
}
}
else
{
lean_dec(v___x_3420_);
lean_dec_ref(v_a_3383_);
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_dec_ref(v_a_3383_);
v___x_3616_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9));
v___x_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
return v___x_3617_;
}
v___jp_3385_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
return v___x_3387_;
}
v___jp_3388_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
v___jp_3391_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
return v___x_3393_;
}
v___jp_3394_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
v___jp_3397_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
v___jp_3400_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
v___jp_3403_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
v___jp_3406_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
return v___x_3408_;
}
v___jp_3409_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
v___jp_3412_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
v___jp_3415_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_3382_ = stack[0].m_obj;
lean_object* v_a_3383_ = stack[1].m_obj;
lean_object* v_res_3618_;
v_res_3618_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v_json_3382_, v_a_3383_);
stack->m_obj
 = v_res_3618_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___boxed(lean_object* v_json_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v_json_3619_, v_a_3620_);
lean_dec(v_json_3619_);
return v_res_3622_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(lean_object* v_json_3629_, lean_object* v_a_3630_){
_start:
{
if (lean_obj_tag(v_json_3629_) == 5)
{
lean_object* v_kvPairs_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_kvPairs_3656_ = lean_ctor_get(v_json_3629_, 0);
v___x_3657_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3658_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3657_);
if (lean_obj_tag(v___x_3658_) == 1)
{
lean_object* v_val_3659_; 
v_val_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_val_3659_);
lean_dec_ref_known(v___x_3658_, 1);
if (lean_obj_tag(v_val_3659_) == 2)
{
lean_object* v_n_3660_; lean_object* v_mantissa_3661_; lean_object* v_exponent_3662_; lean_object* v_natZero_3663_; lean_object* v_intZero_3664_; uint8_t v_isNeg_3665_; 
v_n_3660_ = lean_ctor_get(v_val_3659_, 0);
lean_inc_ref(v_n_3660_);
lean_dec_ref_known(v_val_3659_, 1);
v_mantissa_3661_ = lean_ctor_get(v_n_3660_, 0);
lean_inc(v_mantissa_3661_);
v_exponent_3662_ = lean_ctor_get(v_n_3660_, 1);
lean_inc(v_exponent_3662_);
lean_dec_ref(v_n_3660_);
v_natZero_3663_ = lean_unsigned_to_nat(0u);
v_intZero_3664_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3665_ = lean_int_dec_lt(v_mantissa_3661_, v_intZero_3664_);
if (v_isNeg_3665_ == 0)
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_nat_dec_eq(v_exponent_3662_, v_natZero_3663_);
lean_dec(v_exponent_3662_);
if (v___x_3666_ == 0)
{
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3667_);
if (lean_obj_tag(v___x_3668_) == 1)
{
lean_object* v_val_3669_; 
v_val_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_val_3669_);
lean_dec_ref_known(v___x_3668_, 1);
if (lean_obj_tag(v_val_3669_) == 4)
{
lean_object* v_elems_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_elems_3670_ = lean_ctor_get(v_val_3669_, 0);
lean_inc_ref(v_elems_3670_);
lean_dec_ref_known(v_val_3669_, 1);
v___x_3671_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3671_);
if (lean_obj_tag(v___x_3672_) == 1)
{
lean_object* v_val_3673_; 
v_val_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_val_3673_);
lean_dec_ref_known(v___x_3672_, 1);
if (lean_obj_tag(v_val_3673_) == 2)
{
lean_object* v_n_3674_; lean_object* v_mantissa_3675_; lean_object* v_exponent_3676_; uint8_t v_isNeg_3677_; 
v_n_3674_ = lean_ctor_get(v_val_3673_, 0);
lean_inc_ref(v_n_3674_);
lean_dec_ref_known(v_val_3673_, 1);
v_mantissa_3675_ = lean_ctor_get(v_n_3674_, 0);
lean_inc(v_mantissa_3675_);
v_exponent_3676_ = lean_ctor_get(v_n_3674_, 1);
lean_inc(v_exponent_3676_);
lean_dec_ref(v_n_3674_);
v_isNeg_3677_ = lean_int_dec_lt(v_mantissa_3675_, v_intZero_3664_);
if (v_isNeg_3677_ == 0)
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_nat_dec_eq(v_exponent_3676_, v_natZero_3663_);
lean_dec(v_exponent_3676_);
if (v___x_3678_ == 0)
{
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3638_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2));
v___x_3680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3679_);
if (lean_obj_tag(v___x_3680_) == 1)
{
lean_object* v_val_3681_; 
v_val_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_val_3681_);
lean_dec_ref_known(v___x_3680_, 1);
if (lean_obj_tag(v_val_3681_) == 2)
{
lean_object* v_n_3682_; lean_object* v_mantissa_3683_; lean_object* v_exponent_3684_; uint8_t v_isNeg_3685_; 
v_n_3682_ = lean_ctor_get(v_val_3681_, 0);
lean_inc_ref(v_n_3682_);
lean_dec_ref_known(v_val_3681_, 1);
v_mantissa_3683_ = lean_ctor_get(v_n_3682_, 0);
lean_inc(v_mantissa_3683_);
v_exponent_3684_ = lean_ctor_get(v_n_3682_, 1);
lean_inc(v_exponent_3684_);
lean_dec_ref(v_n_3682_);
v_isNeg_3685_ = lean_int_dec_lt(v_mantissa_3683_, v_intZero_3664_);
if (v_isNeg_3685_ == 0)
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_nat_dec_eq(v_exponent_3684_, v_natZero_3663_);
lean_dec(v_exponent_3684_);
if (v___x_3686_ == 0)
{
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3641_;
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3));
v___x_3688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3687_);
if (lean_obj_tag(v___x_3688_) == 1)
{
lean_object* v_val_3689_; 
v_val_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_val_3689_);
lean_dec_ref_known(v___x_3688_, 1);
if (lean_obj_tag(v_val_3689_) == 2)
{
lean_object* v_n_3690_; lean_object* v_mantissa_3691_; lean_object* v_exponent_3692_; uint8_t v_isNeg_3693_; 
v_n_3690_ = lean_ctor_get(v_val_3689_, 0);
lean_inc_ref(v_n_3690_);
lean_dec_ref_known(v_val_3689_, 1);
v_mantissa_3691_ = lean_ctor_get(v_n_3690_, 0);
lean_inc(v_mantissa_3691_);
v_exponent_3692_ = lean_ctor_get(v_n_3690_, 1);
lean_inc(v_exponent_3692_);
lean_dec_ref(v_n_3690_);
v_isNeg_3693_ = lean_int_dec_lt(v_mantissa_3691_, v_intZero_3664_);
if (v_isNeg_3693_ == 0)
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_nat_dec_eq(v_exponent_3692_, v_natZero_3663_);
lean_dec(v_exponent_3692_);
if (v___x_3694_ == 0)
{
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3644_;
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3695_);
if (lean_obj_tag(v___x_3696_) == 1)
{
lean_object* v_val_3697_; 
v_val_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v___x_3696_, 1);
if (lean_obj_tag(v_val_3697_) == 2)
{
lean_object* v_n_3698_; lean_object* v_mantissa_3699_; lean_object* v_exponent_3700_; uint8_t v_isNeg_3701_; 
v_n_3698_ = lean_ctor_get(v_val_3697_, 0);
lean_inc_ref(v_n_3698_);
lean_dec_ref_known(v_val_3697_, 1);
v_mantissa_3699_ = lean_ctor_get(v_n_3698_, 0);
lean_inc(v_mantissa_3699_);
v_exponent_3700_ = lean_ctor_get(v_n_3698_, 1);
lean_inc(v_exponent_3700_);
lean_dec_ref(v_n_3698_);
v_isNeg_3701_ = lean_int_dec_lt(v_mantissa_3699_, v_intZero_3664_);
if (v_isNeg_3701_ == 0)
{
uint8_t v___x_3702_; 
v___x_3702_ = lean_nat_dec_eq(v_exponent_3700_, v_natZero_3663_);
lean_dec(v_exponent_3700_);
if (v___x_3702_ == 0)
{
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3647_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4));
v___x_3704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3703_);
if (lean_obj_tag(v___x_3704_) == 1)
{
lean_object* v_val_3705_; 
v_val_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_val_3705_);
lean_dec_ref_known(v___x_3704_, 1);
if (lean_obj_tag(v_val_3705_) == 2)
{
lean_object* v_n_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3832_; 
v_n_3706_ = lean_ctor_get(v_val_3705_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_val_3705_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3708_ = v_val_3705_;
v_isShared_3709_ = v_isSharedCheck_3832_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_n_3706_);
lean_dec(v_val_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3832_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_mantissa_3710_; lean_object* v_exponent_3711_; uint8_t v_isNeg_3712_; 
v_mantissa_3710_ = lean_ctor_get(v_n_3706_, 0);
lean_inc(v_mantissa_3710_);
v_exponent_3711_ = lean_ctor_get(v_n_3706_, 1);
lean_inc(v_exponent_3711_);
lean_dec_ref(v_n_3706_);
v_isNeg_3712_ = lean_int_dec_lt(v_mantissa_3710_, v_intZero_3664_);
if (v_isNeg_3712_ == 0)
{
uint8_t v___x_3713_; 
v___x_3713_ = lean_nat_dec_eq(v_exponent_3711_, v_natZero_3663_);
lean_dec(v_exponent_3711_);
if (v___x_3713_ == 0)
{
lean_dec(v_mantissa_3710_);
lean_del_object(v___x_3708_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3650_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3656_, v___x_3714_);
if (lean_obj_tag(v___x_3715_) == 1)
{
lean_object* v_val_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3831_; 
v_val_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3831_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_val_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3831_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
if (lean_obj_tag(v_val_3716_) == 1)
{
uint8_t v_b_3720_; lean_object* v_nameMap_3721_; lean_object* v_a_3722_; lean_object* v___x_3723_; 
v_b_3720_ = lean_ctor_get_uint8(v_val_3716_, 0);
lean_dec_ref_known(v_val_3716_, 0);
v_nameMap_3721_ = lean_ctor_get(v_a_3630_, 1);
v_a_3722_ = lean_nat_abs(v_mantissa_3661_);
lean_dec(v_mantissa_3661_);
v___x_3723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3721_, v_a_3722_);
if (lean_obj_tag(v___x_3723_) == 1)
{
lean_object* v_val_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_a_3722_);
lean_del_object(v___x_3718_);
lean_del_object(v___x_3708_);
v_val_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3821_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_val_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3821_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_a_3728_; lean_object* v_a_3729_; lean_object* v_a_3730_; lean_object* v_a_3731_; lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3728_ = lean_nat_abs(v_mantissa_3675_);
lean_dec(v_mantissa_3675_);
v_a_3729_ = lean_nat_abs(v_mantissa_3683_);
lean_dec(v_mantissa_3683_);
v_a_3730_ = lean_nat_abs(v_mantissa_3691_);
lean_dec(v_mantissa_3691_);
v_a_3731_ = lean_nat_abs(v_mantissa_3699_);
lean_dec(v_mantissa_3699_);
v_a_3732_ = lean_nat_abs(v_mantissa_3710_);
lean_dec(v_mantissa_3710_);
v___x_3733_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3670_, v_a_3630_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3812_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3812_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3812_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_snd_3738_; lean_object* v_fst_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3811_; 
v_snd_3738_ = lean_ctor_get(v_a_3734_, 1);
v_fst_3739_ = lean_ctor_get(v_a_3734_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3741_ = v_a_3734_;
v_isShared_3742_ = v_isSharedCheck_3811_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_snd_3738_);
lean_inc(v_fst_3739_);
lean_dec(v_a_3734_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3811_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v_stream_3743_; lean_object* v_nameMap_3744_; lean_object* v_levelMap_3745_; lean_object* v_exprMap_3746_; lean_object* v_recursorRuleMap_3747_; lean_object* v_constMap_3748_; lean_object* v_constOrder_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3810_; 
v_stream_3743_ = lean_ctor_get(v_snd_3738_, 0);
v_nameMap_3744_ = lean_ctor_get(v_snd_3738_, 1);
v_levelMap_3745_ = lean_ctor_get(v_snd_3738_, 2);
v_exprMap_3746_ = lean_ctor_get(v_snd_3738_, 3);
v_recursorRuleMap_3747_ = lean_ctor_get(v_snd_3738_, 4);
v_constMap_3748_ = lean_ctor_get(v_snd_3738_, 5);
v_constOrder_3749_ = lean_ctor_get(v_snd_3738_, 6);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_snd_3738_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3751_ = v_snd_3738_;
v_isShared_3752_ = v_isSharedCheck_3810_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_constOrder_3749_);
lean_inc(v_constMap_3748_);
lean_inc(v_recursorRuleMap_3747_);
lean_inc(v_exprMap_3746_);
lean_inc(v_levelMap_3745_);
lean_inc(v_nameMap_3744_);
lean_inc(v_stream_3743_);
lean_dec(v_snd_3738_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3810_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3746_, v_a_3728_);
if (lean_obj_tag(v___x_3753_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_a_3728_);
lean_del_object(v___x_3726_);
v_val_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_3800_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_val_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3800_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3744_, v_a_3729_);
if (lean_obj_tag(v___x_3758_) == 1)
{
lean_object* v_val_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3756_);
lean_dec(v_a_3729_);
v_val_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3790_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_val_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3790_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
uint8_t v___x_3763_; 
v___x_3763_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3748_, v_val_3724_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_inc(v_val_3724_);
v___x_3764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3764_, 0, v_val_3724_);
lean_ctor_set(v___x_3764_, 1, v_fst_3739_);
lean_ctor_set(v___x_3764_, 2, v_val_3754_);
v___x_3765_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v_val_3759_);
lean_ctor_set(v___x_3765_, 2, v_a_3730_);
lean_ctor_set(v___x_3765_, 3, v_a_3731_);
lean_ctor_set(v___x_3765_, 4, v_a_3732_);
lean_ctor_set_uint8(v___x_3765_, sizeof(void*)*5, v_b_3720_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 6);
lean_ctor_set(v___x_3761_, 0, v___x_3765_);
v___x_3767_ = v___x_3761_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3768_ = lean_box(0);
lean_inc(v_val_3724_);
v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3748_, v_val_3724_, v___x_3767_);
v___x_3770_ = lean_array_push(v_constOrder_3749_, v_val_3724_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 6, v___x_3770_);
lean_ctor_set(v___x_3751_, 5, v___x_3769_);
v___x_3772_ = v___x_3751_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_stream_3743_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_nameMap_3744_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_levelMap_3745_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v_exprMap_3746_);
lean_ctor_set(v_reuseFailAlloc_3779_, 4, v_recursorRuleMap_3747_);
lean_ctor_set(v_reuseFailAlloc_3779_, 5, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3779_, 6, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3774_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v___x_3772_);
lean_ctor_set(v___x_3741_, 0, v___x_3768_);
v___x_3774_ = v___x_3741_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3774_);
v___x_3776_ = v___x_3736_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_dec(v_val_3759_);
lean_dec(v_val_3754_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_constOrder_3749_);
lean_dec_ref(v_constMap_3748_);
lean_dec_ref(v_recursorRuleMap_3747_);
lean_dec_ref(v_exprMap_3746_);
lean_dec_ref(v_levelMap_3745_);
lean_dec_ref(v_nameMap_3744_);
lean_dec_ref(v_stream_3743_);
lean_del_object(v___x_3741_);
lean_dec(v_fst_3739_);
lean_dec(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec(v_a_3730_);
v___x_3781_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3724_, v___x_3763_);
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
lean_dec_ref(v___x_3782_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 18);
lean_ctor_set(v___x_3761_, 0, v___x_3783_);
v___x_3785_ = v___x_3761_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v___x_3785_);
v___x_3787_ = v___x_3736_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec(v___x_3758_);
lean_dec(v_val_3754_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_constOrder_3749_);
lean_dec_ref(v_constMap_3748_);
lean_dec_ref(v_recursorRuleMap_3747_);
lean_dec_ref(v_exprMap_3746_);
lean_dec_ref(v_levelMap_3745_);
lean_dec_ref(v_nameMap_3744_);
lean_dec_ref(v_stream_3743_);
lean_del_object(v___x_3741_);
lean_dec(v_fst_3739_);
lean_dec(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec(v_val_3724_);
v___x_3791_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3792_ = l_Nat_reprFast(v_a_3729_);
v___x_3793_ = lean_string_append(v___x_3791_, v___x_3792_);
lean_dec_ref(v___x_3792_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set_tag(v___x_3756_, 18);
lean_ctor_set(v___x_3756_, 0, v___x_3793_);
v___x_3795_ = v___x_3756_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v___x_3795_);
v___x_3797_ = v___x_3736_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
lean_dec(v___x_3753_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_constOrder_3749_);
lean_dec_ref(v_constMap_3748_);
lean_dec_ref(v_recursorRuleMap_3747_);
lean_dec_ref(v_exprMap_3746_);
lean_dec_ref(v_levelMap_3745_);
lean_dec_ref(v_nameMap_3744_);
lean_dec_ref(v_stream_3743_);
lean_del_object(v___x_3741_);
lean_dec(v_fst_3739_);
lean_dec(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec(v_val_3724_);
v___x_3801_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3802_ = l_Nat_reprFast(v_a_3728_);
v___x_3803_ = lean_string_append(v___x_3801_, v___x_3802_);
lean_dec_ref(v___x_3802_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set_tag(v___x_3726_, 18);
lean_ctor_set(v___x_3726_, 0, v___x_3803_);
v___x_3805_ = v___x_3726_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v___x_3805_);
v___x_3807_ = v___x_3736_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec(v_a_3728_);
lean_del_object(v___x_3726_);
lean_dec(v_val_3724_);
v_a_3813_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3733_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3733_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_dec(v___x_3723_);
lean_dec(v_mantissa_3710_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec_ref(v_a_3630_);
v___x_3822_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3823_ = l_Nat_reprFast(v_a_3722_);
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set_tag(v___x_3718_, 18);
lean_ctor_set(v___x_3718_, 0, v___x_3824_);
v___x_3826_ = v___x_3718_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 1);
lean_ctor_set(v___x_3708_, 0, v___x_3826_);
v___x_3828_ = v___x_3708_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_del_object(v___x_3718_);
lean_dec(v_val_3716_);
lean_dec(v_mantissa_3710_);
lean_del_object(v___x_3708_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3653_;
}
}
}
else
{
lean_dec(v___x_3715_);
lean_dec(v_mantissa_3710_);
lean_del_object(v___x_3708_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3653_;
}
}
}
else
{
lean_dec(v_exponent_3711_);
lean_dec(v_mantissa_3710_);
lean_del_object(v___x_3708_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3650_;
}
}
}
else
{
lean_dec(v_val_3705_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3650_;
}
}
else
{
lean_dec(v___x_3704_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3650_;
}
}
}
else
{
lean_dec(v_exponent_3700_);
lean_dec(v_mantissa_3699_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3647_;
}
}
else
{
lean_dec(v_val_3697_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3647_;
}
}
else
{
lean_dec(v___x_3696_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3647_;
}
}
}
else
{
lean_dec(v_exponent_3692_);
lean_dec(v_mantissa_3691_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3644_;
}
}
else
{
lean_dec(v_val_3689_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3644_;
}
}
else
{
lean_dec(v___x_3688_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3644_;
}
}
}
else
{
lean_dec(v_exponent_3684_);
lean_dec(v_mantissa_3683_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3641_;
}
}
else
{
lean_dec(v_val_3681_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3641_;
}
}
else
{
lean_dec(v___x_3680_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3641_;
}
}
}
else
{
lean_dec(v_exponent_3676_);
lean_dec(v_mantissa_3675_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3638_;
}
}
else
{
lean_dec(v_val_3673_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3638_;
}
}
else
{
lean_dec(v___x_3672_);
lean_dec_ref(v_elems_3670_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3638_;
}
}
else
{
lean_dec(v_val_3669_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3635_;
}
}
else
{
lean_dec(v___x_3668_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3635_;
}
}
}
else
{
lean_dec(v_exponent_3662_);
lean_dec(v_mantissa_3661_);
lean_dec_ref(v_a_3630_);
goto v___jp_3632_;
}
}
else
{
lean_dec(v_val_3659_);
lean_dec_ref(v_a_3630_);
goto v___jp_3632_;
}
}
else
{
lean_dec(v___x_3658_);
lean_dec_ref(v_a_3630_);
goto v___jp_3632_;
}
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v_a_3630_);
v___x_3833_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
v___jp_3632_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
return v___x_3634_;
}
v___jp_3635_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
return v___x_3637_;
}
v___jp_3638_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
v___jp_3641_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
return v___x_3643_;
}
v___jp_3644_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
v___jp_3647_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
return v___x_3649_;
}
v___jp_3650_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
v___jp_3653_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_3629_ = stack[0].m_obj;
lean_object* v_a_3630_ = stack[1].m_obj;
lean_object* v_res_3835_;
v_res_3835_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v_json_3629_, v_a_3630_);
stack->m_obj
 = v_res_3835_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___boxed(lean_object* v_json_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v_json_3836_, v_a_3837_);
lean_dec(v_json_3836_);
return v_res_3839_;
}
}
lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(lean_object* v_x_3845_, lean_object* v_x_3846_, lean_object* v___y_3847_){
_start:
{
if (lean_obj_tag(v_x_3845_) == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3858_ = l_List_reverse___redArg(v_x_3846_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
lean_ctor_set(v___x_3859_, 1, v___y_3847_);
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
return v___x_3860_;
}
else
{
lean_object* v_head_3861_; 
v_head_3861_ = lean_ctor_get(v_x_3845_, 0);
lean_inc(v_head_3861_);
if (lean_obj_tag(v_head_3861_) == 5)
{
lean_object* v_tail_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3937_; 
v_tail_3862_ = lean_ctor_get(v_x_3845_, 1);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3845_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_x_3845_, 0);
lean_dec(v_unused_3938_);
v___x_3864_ = v_x_3845_;
v_isShared_3865_ = v_isSharedCheck_3937_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_tail_3862_);
lean_dec(v_x_3845_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3937_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_kvPairs_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v_kvPairs_3866_ = lean_ctor_get(v_head_3861_, 0);
lean_inc(v_kvPairs_3866_);
lean_dec_ref_known(v_head_3861_, 1);
v___x_3867_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3866_, v___x_3867_);
if (lean_obj_tag(v___x_3868_) == 1)
{
lean_object* v_val_3869_; 
v_val_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v___x_3868_, 1);
if (lean_obj_tag(v_val_3869_) == 2)
{
lean_object* v_n_3870_; lean_object* v_mantissa_3871_; lean_object* v_exponent_3872_; lean_object* v_natZero_3873_; lean_object* v_intZero_3874_; uint8_t v_isNeg_3875_; 
v_n_3870_ = lean_ctor_get(v_val_3869_, 0);
lean_inc_ref(v_n_3870_);
lean_dec_ref_known(v_val_3869_, 1);
v_mantissa_3871_ = lean_ctor_get(v_n_3870_, 0);
lean_inc(v_mantissa_3871_);
v_exponent_3872_ = lean_ctor_get(v_n_3870_, 1);
lean_inc(v_exponent_3872_);
lean_dec_ref(v_n_3870_);
v_natZero_3873_ = lean_unsigned_to_nat(0u);
v_intZero_3874_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3875_ = lean_int_dec_lt(v_mantissa_3871_, v_intZero_3874_);
if (v_isNeg_3875_ == 0)
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_nat_dec_eq(v_exponent_3872_, v_natZero_3873_);
lean_dec(v_exponent_3872_);
if (v___x_3876_ == 0)
{
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3849_;
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2));
v___x_3878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3866_, v___x_3877_);
if (lean_obj_tag(v___x_3878_) == 1)
{
lean_object* v_val_3879_; 
v_val_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_val_3879_);
lean_dec_ref_known(v___x_3878_, 1);
if (lean_obj_tag(v_val_3879_) == 2)
{
lean_object* v_n_3880_; lean_object* v_mantissa_3881_; lean_object* v_exponent_3882_; uint8_t v_isNeg_3883_; 
v_n_3880_ = lean_ctor_get(v_val_3879_, 0);
lean_inc_ref(v_n_3880_);
lean_dec_ref_known(v_val_3879_, 1);
v_mantissa_3881_ = lean_ctor_get(v_n_3880_, 0);
lean_inc(v_mantissa_3881_);
v_exponent_3882_ = lean_ctor_get(v_n_3880_, 1);
lean_inc(v_exponent_3882_);
lean_dec_ref(v_n_3880_);
v_isNeg_3883_ = lean_int_dec_lt(v_mantissa_3881_, v_intZero_3874_);
if (v_isNeg_3883_ == 0)
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_nat_dec_eq(v_exponent_3882_, v_natZero_3873_);
lean_dec(v_exponent_3882_);
if (v___x_3884_ == 0)
{
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3852_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3));
v___x_3886_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3866_, v___x_3885_);
lean_dec(v_kvPairs_3866_);
if (lean_obj_tag(v___x_3886_) == 1)
{
lean_object* v_val_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3936_; 
v_val_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3936_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_val_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3936_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
if (lean_obj_tag(v_val_3887_) == 2)
{
lean_object* v_n_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3935_; 
v_n_3891_ = lean_ctor_get(v_val_3887_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_val_3887_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3893_ = v_val_3887_;
v_isShared_3894_ = v_isSharedCheck_3935_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_n_3891_);
lean_dec(v_val_3887_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3935_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v_mantissa_3895_; lean_object* v_exponent_3896_; uint8_t v_isNeg_3897_; 
v_mantissa_3895_ = lean_ctor_get(v_n_3891_, 0);
lean_inc(v_mantissa_3895_);
v_exponent_3896_ = lean_ctor_get(v_n_3891_, 1);
lean_inc(v_exponent_3896_);
lean_dec_ref(v_n_3891_);
v_isNeg_3897_ = lean_int_dec_lt(v_mantissa_3895_, v_intZero_3874_);
if (v_isNeg_3897_ == 0)
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_nat_dec_eq(v_exponent_3896_, v_natZero_3873_);
lean_dec(v_exponent_3896_);
if (v___x_3898_ == 0)
{
lean_dec(v_mantissa_3895_);
lean_del_object(v___x_3893_);
lean_del_object(v___x_3889_);
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3855_;
}
else
{
lean_object* v_nameMap_3899_; lean_object* v_exprMap_3900_; lean_object* v_a_3901_; lean_object* v___x_3902_; 
v_nameMap_3899_ = lean_ctor_get(v___y_3847_, 1);
v_exprMap_3900_ = lean_ctor_get(v___y_3847_, 3);
v_a_3901_ = lean_nat_abs(v_mantissa_3871_);
lean_dec(v_mantissa_3871_);
v___x_3902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3899_, v_a_3901_);
if (lean_obj_tag(v___x_3902_) == 1)
{
lean_object* v_val_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_a_3901_);
lean_del_object(v___x_3889_);
v_val_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3925_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_val_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3925_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v_a_3907_; lean_object* v___x_3908_; 
v_a_3907_ = lean_nat_abs(v_mantissa_3895_);
lean_dec(v_mantissa_3895_);
v___x_3908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3900_, v_a_3907_);
if (lean_obj_tag(v___x_3908_) == 1)
{
lean_object* v_val_3909_; lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_a_3907_);
lean_del_object(v___x_3905_);
lean_del_object(v___x_3893_);
v_val_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v_a_3910_ = lean_nat_abs(v_mantissa_3881_);
lean_dec(v_mantissa_3881_);
v___x_3911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3911_, 0, v_val_3903_);
lean_ctor_set(v___x_3911_, 1, v_a_3910_);
lean_ctor_set(v___x_3911_, 2, v_val_3909_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v_x_3846_);
lean_ctor_set(v___x_3864_, 0, v___x_3911_);
v___x_3913_ = v___x_3864_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_x_3846_);
v___x_3913_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
v_x_3845_ = v_tail_3862_;
v_x_3846_ = v___x_3913_;
goto _start;
}
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_dec(v___x_3908_);
lean_dec(v_val_3903_);
lean_dec(v_mantissa_3881_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
v___x_3916_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3917_ = l_Nat_reprFast(v_a_3907_);
v___x_3918_ = lean_string_append(v___x_3916_, v___x_3917_);
lean_dec_ref(v___x_3917_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set_tag(v___x_3905_, 18);
lean_ctor_set(v___x_3905_, 0, v___x_3918_);
v___x_3920_ = v___x_3905_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set_tag(v___x_3893_, 1);
lean_ctor_set(v___x_3893_, 0, v___x_3920_);
v___x_3922_ = v___x_3893_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
lean_dec(v___x_3902_);
lean_dec(v_mantissa_3895_);
lean_dec(v_mantissa_3881_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
v___x_3926_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3927_ = l_Nat_reprFast(v_a_3901_);
v___x_3928_ = lean_string_append(v___x_3926_, v___x_3927_);
lean_dec_ref(v___x_3927_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set_tag(v___x_3893_, 18);
lean_ctor_set(v___x_3893_, 0, v___x_3928_);
v___x_3930_ = v___x_3893_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3930_);
v___x_3932_ = v___x_3889_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
else
{
lean_dec(v_exponent_3896_);
lean_dec(v_mantissa_3895_);
lean_del_object(v___x_3893_);
lean_del_object(v___x_3889_);
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3855_;
}
}
}
else
{
lean_del_object(v___x_3889_);
lean_dec(v_val_3887_);
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3855_;
}
}
}
else
{
lean_dec(v___x_3886_);
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3855_;
}
}
}
else
{
lean_dec(v_exponent_3882_);
lean_dec(v_mantissa_3881_);
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3852_;
}
}
else
{
lean_dec(v_val_3879_);
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3852_;
}
}
else
{
lean_dec(v___x_3878_);
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3852_;
}
}
}
else
{
lean_dec(v_exponent_3872_);
lean_dec(v_mantissa_3871_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3849_;
}
}
else
{
lean_dec(v_val_3869_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3849_;
}
}
else
{
lean_dec(v___x_3868_);
lean_dec(v_kvPairs_3866_);
lean_del_object(v___x_3864_);
lean_dec(v_tail_3862_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
goto v___jp_3849_;
}
}
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec_ref_known(v_x_3845_, 2);
lean_dec(v_head_3861_);
lean_dec_ref(v___y_3847_);
lean_dec(v_x_3846_);
v___x_3939_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
v___jp_3849_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
return v___x_3851_;
}
v___jp_3852_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
return v___x_3854_;
}
v___jp_3855_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3845_ = stack[0].m_obj;
lean_object* v_x_3846_ = stack[1].m_obj;
lean_object* v___y_3847_ = stack[2].m_obj;
lean_object* v_res_3941_;
v_res_3941_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v_x_3845_, v_x_3846_, v___y_3847_);
stack->m_obj
 = v_res_3941_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___boxed(lean_object* v_x_3942_, lean_object* v_x_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v_x_3942_, v_x_3943_, v___y_3944_);
return v_res_3946_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(lean_object* v_json_3951_, lean_object* v_a_3952_){
_start:
{
if (lean_obj_tag(v_json_3951_) == 5)
{
lean_object* v_kvPairs_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_kvPairs_3987_ = lean_ctor_get(v_json_3951_, 0);
v___x_3988_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_3988_);
if (lean_obj_tag(v___x_3989_) == 1)
{
lean_object* v_val_3990_; 
v_val_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_val_3990_);
lean_dec_ref_known(v___x_3989_, 1);
if (lean_obj_tag(v_val_3990_) == 2)
{
lean_object* v_n_3991_; lean_object* v_mantissa_3992_; lean_object* v_exponent_3993_; lean_object* v_natZero_3994_; lean_object* v_intZero_3995_; uint8_t v_isNeg_3996_; 
v_n_3991_ = lean_ctor_get(v_val_3990_, 0);
lean_inc_ref(v_n_3991_);
lean_dec_ref_known(v_val_3990_, 1);
v_mantissa_3992_ = lean_ctor_get(v_n_3991_, 0);
lean_inc(v_mantissa_3992_);
v_exponent_3993_ = lean_ctor_get(v_n_3991_, 1);
lean_inc(v_exponent_3993_);
lean_dec_ref(v_n_3991_);
v_natZero_3994_ = lean_unsigned_to_nat(0u);
v_intZero_3995_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3996_ = lean_int_dec_lt(v_mantissa_3992_, v_intZero_3995_);
if (v_isNeg_3996_ == 0)
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_nat_dec_eq(v_exponent_3993_, v_natZero_3994_);
lean_dec(v_exponent_3993_);
if (v___x_3997_ == 0)
{
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3954_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3999_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_3998_);
if (lean_obj_tag(v___x_3999_) == 1)
{
lean_object* v_val_4000_; 
v_val_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_val_4000_);
lean_dec_ref_known(v___x_3999_, 1);
if (lean_obj_tag(v_val_4000_) == 4)
{
lean_object* v_elems_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v_elems_4001_ = lean_ctor_get(v_val_4000_, 0);
lean_inc_ref(v_elems_4001_);
lean_dec_ref_known(v_val_4000_, 1);
v___x_4002_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_4003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4002_);
if (lean_obj_tag(v___x_4003_) == 1)
{
lean_object* v_val_4004_; 
v_val_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_val_4004_);
lean_dec_ref_known(v___x_4003_, 1);
if (lean_obj_tag(v_val_4004_) == 2)
{
lean_object* v_n_4005_; lean_object* v_mantissa_4006_; lean_object* v_exponent_4007_; uint8_t v_isNeg_4008_; 
v_n_4005_ = lean_ctor_get(v_val_4004_, 0);
lean_inc_ref(v_n_4005_);
lean_dec_ref_known(v_val_4004_, 1);
v_mantissa_4006_ = lean_ctor_get(v_n_4005_, 0);
lean_inc(v_mantissa_4006_);
v_exponent_4007_ = lean_ctor_get(v_n_4005_, 1);
lean_inc(v_exponent_4007_);
lean_dec_ref(v_n_4005_);
v_isNeg_4008_ = lean_int_dec_lt(v_mantissa_4006_, v_intZero_3995_);
if (v_isNeg_4008_ == 0)
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_nat_dec_eq(v_exponent_4007_, v_natZero_3994_);
lean_dec(v_exponent_4007_);
if (v___x_4009_ == 0)
{
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3960_;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_4011_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4010_);
if (lean_obj_tag(v___x_4011_) == 1)
{
lean_object* v_val_4012_; 
v_val_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_val_4012_);
lean_dec_ref_known(v___x_4011_, 1);
if (lean_obj_tag(v_val_4012_) == 4)
{
lean_object* v_elems_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_elems_4013_ = lean_ctor_get(v_val_4012_, 0);
lean_inc_ref(v_elems_4013_);
lean_dec_ref_known(v_val_4012_, 1);
v___x_4014_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_4015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4014_);
if (lean_obj_tag(v___x_4015_) == 1)
{
lean_object* v_val_4016_; 
v_val_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_val_4016_);
lean_dec_ref_known(v___x_4015_, 1);
if (lean_obj_tag(v_val_4016_) == 2)
{
lean_object* v_n_4017_; lean_object* v_mantissa_4018_; lean_object* v_exponent_4019_; uint8_t v_isNeg_4020_; 
v_n_4017_ = lean_ctor_get(v_val_4016_, 0);
lean_inc_ref(v_n_4017_);
lean_dec_ref_known(v_val_4016_, 1);
v_mantissa_4018_ = lean_ctor_get(v_n_4017_, 0);
lean_inc(v_mantissa_4018_);
v_exponent_4019_ = lean_ctor_get(v_n_4017_, 1);
lean_inc(v_exponent_4019_);
lean_dec_ref(v_n_4017_);
v_isNeg_4020_ = lean_int_dec_lt(v_mantissa_4018_, v_intZero_3995_);
if (v_isNeg_4020_ == 0)
{
uint8_t v___x_4021_; 
v___x_4021_ = lean_nat_dec_eq(v_exponent_4019_, v_natZero_3994_);
lean_dec(v_exponent_4019_);
if (v___x_4021_ == 0)
{
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3966_;
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_4023_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4022_);
if (lean_obj_tag(v___x_4023_) == 1)
{
lean_object* v_val_4024_; 
v_val_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_val_4024_);
lean_dec_ref_known(v___x_4023_, 1);
if (lean_obj_tag(v_val_4024_) == 2)
{
lean_object* v_n_4025_; lean_object* v_mantissa_4026_; lean_object* v_exponent_4027_; uint8_t v_isNeg_4028_; 
v_n_4025_ = lean_ctor_get(v_val_4024_, 0);
lean_inc_ref(v_n_4025_);
lean_dec_ref_known(v_val_4024_, 1);
v_mantissa_4026_ = lean_ctor_get(v_n_4025_, 0);
lean_inc(v_mantissa_4026_);
v_exponent_4027_ = lean_ctor_get(v_n_4025_, 1);
lean_inc(v_exponent_4027_);
lean_dec_ref(v_n_4025_);
v_isNeg_4028_ = lean_int_dec_lt(v_mantissa_4026_, v_intZero_3995_);
if (v_isNeg_4028_ == 0)
{
uint8_t v___x_4029_; 
v___x_4029_ = lean_nat_dec_eq(v_exponent_4027_, v_natZero_3994_);
lean_dec(v_exponent_4027_);
if (v___x_4029_ == 0)
{
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3969_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0));
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 1)
{
lean_object* v_val_4032_; 
v_val_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v___x_4031_, 1);
if (lean_obj_tag(v_val_4032_) == 2)
{
lean_object* v_n_4033_; lean_object* v_mantissa_4034_; lean_object* v_exponent_4035_; uint8_t v_isNeg_4036_; 
v_n_4033_ = lean_ctor_get(v_val_4032_, 0);
lean_inc_ref(v_n_4033_);
lean_dec_ref_known(v_val_4032_, 1);
v_mantissa_4034_ = lean_ctor_get(v_n_4033_, 0);
lean_inc(v_mantissa_4034_);
v_exponent_4035_ = lean_ctor_get(v_n_4033_, 1);
lean_inc(v_exponent_4035_);
lean_dec_ref(v_n_4033_);
v_isNeg_4036_ = lean_int_dec_lt(v_mantissa_4034_, v_intZero_3995_);
if (v_isNeg_4036_ == 0)
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_nat_dec_eq(v_exponent_4035_, v_natZero_3994_);
lean_dec(v_exponent_4035_);
if (v___x_4037_ == 0)
{
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3972_;
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1));
v___x_4039_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4038_);
if (lean_obj_tag(v___x_4039_) == 1)
{
lean_object* v_val_4040_; 
v_val_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v___x_4039_, 1);
if (lean_obj_tag(v_val_4040_) == 2)
{
lean_object* v_n_4041_; lean_object* v_mantissa_4042_; lean_object* v_exponent_4043_; uint8_t v_isNeg_4044_; 
v_n_4041_ = lean_ctor_get(v_val_4040_, 0);
lean_inc_ref(v_n_4041_);
lean_dec_ref_known(v_val_4040_, 1);
v_mantissa_4042_ = lean_ctor_get(v_n_4041_, 0);
lean_inc(v_mantissa_4042_);
v_exponent_4043_ = lean_ctor_get(v_n_4041_, 1);
lean_inc(v_exponent_4043_);
lean_dec_ref(v_n_4041_);
v_isNeg_4044_ = lean_int_dec_lt(v_mantissa_4042_, v_intZero_3995_);
if (v_isNeg_4044_ == 0)
{
uint8_t v___x_4045_; 
v___x_4045_ = lean_nat_dec_eq(v_exponent_4043_, v_natZero_3994_);
lean_dec(v_exponent_4043_);
if (v___x_4045_ == 0)
{
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3975_;
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2));
v___x_4047_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4046_);
if (lean_obj_tag(v___x_4047_) == 1)
{
lean_object* v_val_4048_; 
v_val_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v___x_4047_, 1);
if (lean_obj_tag(v_val_4048_) == 1)
{
uint8_t v_b_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_b_4049_ = lean_ctor_get_uint8(v_val_4048_, 0);
lean_dec_ref_known(v_val_4048_, 0);
v___x_4050_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3));
v___x_4051_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4050_);
if (lean_obj_tag(v___x_4051_) == 1)
{
lean_object* v_val_4052_; 
v_val_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_val_4052_);
lean_dec_ref_known(v___x_4051_, 1);
if (lean_obj_tag(v_val_4052_) == 4)
{
lean_object* v_elems_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4191_; 
v_elems_4053_ = lean_ctor_get(v_val_4052_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_val_4052_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4055_ = v_val_4052_;
v_isShared_4056_ = v_isSharedCheck_4191_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_elems_4053_);
lean_dec(v_val_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4191_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_4058_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3987_, v___x_4057_);
if (lean_obj_tag(v___x_4058_) == 1)
{
lean_object* v_val_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4190_; 
v_val_4059_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4061_ = v___x_4058_;
v_isShared_4062_ = v_isSharedCheck_4190_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_val_4059_);
lean_dec(v___x_4058_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4190_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
if (lean_obj_tag(v_val_4059_) == 1)
{
uint8_t v_b_4063_; lean_object* v_nameMap_4064_; lean_object* v_a_4065_; lean_object* v___x_4066_; 
v_b_4063_ = lean_ctor_get_uint8(v_val_4059_, 0);
lean_dec_ref_known(v_val_4059_, 0);
v_nameMap_4064_ = lean_ctor_get(v_a_3952_, 1);
v_a_4065_ = lean_nat_abs(v_mantissa_3992_);
lean_dec(v_mantissa_3992_);
v___x_4066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4066_) == 1)
{
lean_object* v_val_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v_a_4065_);
lean_del_object(v___x_4061_);
lean_del_object(v___x_4055_);
v_val_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4180_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_val_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4180_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v_a_4071_; lean_object* v_a_4072_; lean_object* v_a_4073_; lean_object* v_a_4074_; lean_object* v_a_4075_; lean_object* v___x_4076_; 
v_a_4071_ = lean_nat_abs(v_mantissa_4006_);
lean_dec(v_mantissa_4006_);
v_a_4072_ = lean_nat_abs(v_mantissa_4018_);
lean_dec(v_mantissa_4018_);
v_a_4073_ = lean_nat_abs(v_mantissa_4026_);
lean_dec(v_mantissa_4026_);
v_a_4074_ = lean_nat_abs(v_mantissa_4034_);
lean_dec(v_mantissa_4034_);
v_a_4075_ = lean_nat_abs(v_mantissa_4042_);
lean_dec(v_mantissa_4042_);
v___x_4076_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_4001_, v_a_3952_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4171_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4171_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4171_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v_snd_4081_; lean_object* v_fst_4082_; lean_object* v_exprMap_4083_; lean_object* v___x_4084_; 
v_snd_4081_ = lean_ctor_get(v_a_4077_, 1);
lean_inc(v_snd_4081_);
v_fst_4082_ = lean_ctor_get(v_a_4077_, 0);
lean_inc(v_fst_4082_);
lean_dec(v_a_4077_);
v_exprMap_4083_ = lean_ctor_get(v_snd_4081_, 3);
v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_4083_, v_a_4071_);
if (lean_obj_tag(v___x_4084_) == 1)
{
lean_object* v_val_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4161_; 
lean_del_object(v___x_4079_);
lean_dec(v_a_4071_);
lean_del_object(v___x_4069_);
v_val_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4161_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_val_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4161_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; 
v___x_4089_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_4013_, v_snd_4081_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v_fst_4091_; lean_object* v_snd_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v_fst_4091_ = lean_ctor_get(v_a_4090_, 0);
lean_inc(v_fst_4091_);
v_snd_4092_ = lean_ctor_get(v_a_4090_, 1);
lean_inc(v_snd_4092_);
lean_dec(v_a_4090_);
v___x_4093_ = lean_array_to_list(v_elems_4053_);
v___x_4094_ = lean_box(0);
v___x_4095_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v___x_4093_, v___x_4094_, v_snd_4092_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4144_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4144_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4144_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v_snd_4100_; lean_object* v_fst_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4143_; 
v_snd_4100_ = lean_ctor_get(v_a_4096_, 1);
v_fst_4101_ = lean_ctor_get(v_a_4096_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4103_ = v_a_4096_;
v_isShared_4104_ = v_isSharedCheck_4143_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_snd_4100_);
lean_inc(v_fst_4101_);
lean_dec(v_a_4096_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4143_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v_stream_4105_; lean_object* v_nameMap_4106_; lean_object* v_levelMap_4107_; lean_object* v_exprMap_4108_; lean_object* v_recursorRuleMap_4109_; lean_object* v_constMap_4110_; lean_object* v_constOrder_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4142_; 
v_stream_4105_ = lean_ctor_get(v_snd_4100_, 0);
v_nameMap_4106_ = lean_ctor_get(v_snd_4100_, 1);
v_levelMap_4107_ = lean_ctor_get(v_snd_4100_, 2);
v_exprMap_4108_ = lean_ctor_get(v_snd_4100_, 3);
v_recursorRuleMap_4109_ = lean_ctor_get(v_snd_4100_, 4);
v_constMap_4110_ = lean_ctor_get(v_snd_4100_, 5);
v_constOrder_4111_ = lean_ctor_get(v_snd_4100_, 6);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_snd_4100_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4113_ = v_snd_4100_;
v_isShared_4114_ = v_isSharedCheck_4142_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_constOrder_4111_);
lean_inc(v_constMap_4110_);
lean_inc(v_recursorRuleMap_4109_);
lean_inc(v_exprMap_4108_);
lean_inc(v_levelMap_4107_);
lean_inc(v_nameMap_4106_);
lean_inc(v_stream_4105_);
lean_dec(v_snd_4100_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4142_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
uint8_t v___x_4115_; 
v___x_4115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_4110_, v_val_4067_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
lean_inc(v_val_4067_);
v___x_4116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4116_, 0, v_val_4067_);
lean_ctor_set(v___x_4116_, 1, v_fst_4082_);
lean_ctor_set(v___x_4116_, 2, v_val_4085_);
v___x_4117_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
lean_ctor_set(v___x_4117_, 1, v_fst_4091_);
lean_ctor_set(v___x_4117_, 2, v_a_4072_);
lean_ctor_set(v___x_4117_, 3, v_a_4073_);
lean_ctor_set(v___x_4117_, 4, v_a_4074_);
lean_ctor_set(v___x_4117_, 5, v_a_4075_);
lean_ctor_set(v___x_4117_, 6, v_fst_4101_);
lean_ctor_set_uint8(v___x_4117_, sizeof(void*)*7, v_b_4049_);
lean_ctor_set_uint8(v___x_4117_, sizeof(void*)*7 + 1, v_b_4063_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 7);
lean_ctor_set(v___x_4087_, 0, v___x_4117_);
v___x_4119_ = v___x_4087_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v___x_4120_ = lean_box(0);
lean_inc(v_val_4067_);
v___x_4121_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_4110_, v_val_4067_, v___x_4119_);
v___x_4122_ = lean_array_push(v_constOrder_4111_, v_val_4067_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 6, v___x_4122_);
lean_ctor_set(v___x_4113_, 5, v___x_4121_);
v___x_4124_ = v___x_4113_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_stream_4105_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_nameMap_4106_);
lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_levelMap_4107_);
lean_ctor_set(v_reuseFailAlloc_4131_, 3, v_exprMap_4108_);
lean_ctor_set(v_reuseFailAlloc_4131_, 4, v_recursorRuleMap_4109_);
lean_ctor_set(v_reuseFailAlloc_4131_, 5, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4131_, 6, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4126_; 
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4124_);
lean_ctor_set(v___x_4103_, 0, v___x_4120_);
v___x_4126_ = v___x_4103_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4120_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4128_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4126_);
v___x_4128_ = v___x_4098_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
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
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
lean_del_object(v___x_4113_);
lean_dec_ref(v_constOrder_4111_);
lean_dec_ref(v_constMap_4110_);
lean_dec_ref(v_recursorRuleMap_4109_);
lean_dec_ref(v_exprMap_4108_);
lean_dec_ref(v_levelMap_4107_);
lean_dec_ref(v_nameMap_4106_);
lean_dec_ref(v_stream_4105_);
lean_del_object(v___x_4103_);
lean_dec(v_fst_4101_);
lean_dec(v_fst_4091_);
lean_dec(v_val_4085_);
lean_dec(v_fst_4082_);
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec(v_a_4072_);
v___x_4133_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_4134_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_4067_, v___x_4115_);
v___x_4135_ = lean_string_append(v___x_4133_, v___x_4134_);
lean_dec_ref(v___x_4134_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 18);
lean_ctor_set(v___x_4087_, 0, v___x_4135_);
v___x_4137_ = v___x_4087_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4139_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set_tag(v___x_4098_, 1);
lean_ctor_set(v___x_4098_, 0, v___x_4137_);
v___x_4139_ = v___x_4098_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_fst_4091_);
lean_del_object(v___x_4087_);
lean_dec(v_val_4085_);
lean_dec(v_fst_4082_);
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec(v_val_4067_);
v_a_4145_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4095_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4095_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_del_object(v___x_4087_);
lean_dec(v_val_4085_);
lean_dec(v_fst_4082_);
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec(v_val_4067_);
lean_dec_ref(v_elems_4053_);
v_a_4153_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4089_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4089_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
lean_dec(v___x_4084_);
lean_dec(v_fst_4082_);
lean_dec(v_snd_4081_);
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec(v_val_4067_);
lean_dec_ref(v_elems_4053_);
lean_dec_ref(v_elems_4013_);
v___x_4162_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_4163_ = l_Nat_reprFast(v_a_4071_);
v___x_4164_ = lean_string_append(v___x_4162_, v___x_4163_);
lean_dec_ref(v___x_4163_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 18);
lean_ctor_set(v___x_4069_, 0, v___x_4164_);
v___x_4166_ = v___x_4069_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4168_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set_tag(v___x_4079_, 1);
lean_ctor_set(v___x_4079_, 0, v___x_4166_);
v___x_4168_ = v___x_4079_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec(v_a_4071_);
lean_del_object(v___x_4069_);
lean_dec(v_val_4067_);
lean_dec_ref(v_elems_4053_);
lean_dec_ref(v_elems_4013_);
v_a_4172_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4076_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4076_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
else
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4185_; 
lean_dec(v___x_4066_);
lean_dec_ref(v_elems_4053_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec_ref(v_a_3952_);
v___x_4181_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_4182_ = l_Nat_reprFast(v_a_4065_);
v___x_4183_ = lean_string_append(v___x_4181_, v___x_4182_);
lean_dec_ref(v___x_4182_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set_tag(v___x_4061_, 18);
lean_ctor_set(v___x_4061_, 0, v___x_4183_);
v___x_4185_ = v___x_4061_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4187_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 1);
lean_ctor_set(v___x_4055_, 0, v___x_4185_);
v___x_4187_ = v___x_4055_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_del_object(v___x_4061_);
lean_dec(v_val_4059_);
lean_del_object(v___x_4055_);
lean_dec_ref(v_elems_4053_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3984_;
}
}
}
else
{
lean_dec(v___x_4058_);
lean_del_object(v___x_4055_);
lean_dec_ref(v_elems_4053_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3984_;
}
}
}
else
{
lean_dec(v_val_4052_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v___x_4051_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v_val_4048_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3978_;
}
}
else
{
lean_dec(v___x_4047_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3978_;
}
}
}
else
{
lean_dec(v_exponent_4043_);
lean_dec(v_mantissa_4042_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3975_;
}
}
else
{
lean_dec(v_val_4040_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3975_;
}
}
else
{
lean_dec(v___x_4039_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3975_;
}
}
}
else
{
lean_dec(v_exponent_4035_);
lean_dec(v_mantissa_4034_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3972_;
}
}
else
{
lean_dec(v_val_4032_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3972_;
}
}
else
{
lean_dec(v___x_4031_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3972_;
}
}
}
else
{
lean_dec(v_exponent_4027_);
lean_dec(v_mantissa_4026_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3969_;
}
}
else
{
lean_dec(v_val_4024_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3969_;
}
}
else
{
lean_dec(v___x_4023_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3969_;
}
}
}
else
{
lean_dec(v_exponent_4019_);
lean_dec(v_mantissa_4018_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3966_;
}
}
else
{
lean_dec(v_val_4016_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3966_;
}
}
else
{
lean_dec(v___x_4015_);
lean_dec_ref(v_elems_4013_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3966_;
}
}
else
{
lean_dec(v_val_4012_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3963_;
}
}
else
{
lean_dec(v___x_4011_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3963_;
}
}
}
else
{
lean_dec(v_exponent_4007_);
lean_dec(v_mantissa_4006_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3960_;
}
}
else
{
lean_dec(v_val_4004_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3960_;
}
}
else
{
lean_dec(v___x_4003_);
lean_dec_ref(v_elems_4001_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3960_;
}
}
else
{
lean_dec(v_val_4000_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3957_;
}
}
else
{
lean_dec(v___x_3999_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3957_;
}
}
}
else
{
lean_dec(v_exponent_3993_);
lean_dec(v_mantissa_3992_);
lean_dec_ref(v_a_3952_);
goto v___jp_3954_;
}
}
else
{
lean_dec(v_val_3990_);
lean_dec_ref(v_a_3952_);
goto v___jp_3954_;
}
}
else
{
lean_dec(v___x_3989_);
lean_dec_ref(v_a_3952_);
goto v___jp_3954_;
}
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
lean_dec_ref(v_a_3952_);
v___x_4192_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
return v___x_4193_;
}
v___jp_3954_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
v___jp_3957_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
v___jp_3960_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
return v___x_3962_;
}
v___jp_3963_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
v___jp_3966_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
v___jp_3969_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
v___jp_3972_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
v___jp_3975_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
v___jp_3978_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
v___jp_3981_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
v___jp_3984_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3985_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_json_3951_ = stack[0].m_obj;
lean_object* v_a_3952_ = stack[1].m_obj;
lean_object* v_res_4194_;
v_res_4194_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v_json_3951_, v_a_3952_);
stack->m_obj
 = v_res_4194_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___boxed(lean_object* v_json_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v_json_4195_, v_a_4196_);
lean_dec(v_json_4195_);
return v_res_4198_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(lean_object* v_as_4199_, size_t v_i_4200_, size_t v_stop_4201_, lean_object* v_b_4202_, lean_object* v___y_4203_){
_start:
{
uint8_t v___x_4205_; 
v___x_4205_ = lean_usize_dec_eq(v_i_4200_, v_stop_4201_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = lean_array_uget_borrowed(v_as_4199_, v_i_4200_);
v___x_4207_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v___x_4206_, v___y_4203_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v_fst_4209_; lean_object* v_snd_4210_; size_t v___x_4211_; size_t v___x_4212_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v_fst_4209_ = lean_ctor_get(v_a_4208_, 0);
lean_inc(v_fst_4209_);
v_snd_4210_ = lean_ctor_get(v_a_4208_, 1);
lean_inc(v_snd_4210_);
lean_dec(v_a_4208_);
v___x_4211_ = ((size_t)1ULL);
v___x_4212_ = lean_usize_add(v_i_4200_, v___x_4211_);
v_i_4200_ = v___x_4212_;
v_b_4202_ = v_fst_4209_;
v___y_4203_ = v_snd_4210_;
goto _start;
}
else
{
return v___x_4207_;
}
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_b_4202_);
lean_ctor_set(v___x_4214_, 1, v___y_4203_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4199_ = stack[0].m_obj;
size_t v_i_4200_ = stack[1].m_num;
size_t v_stop_4201_ = stack[2].m_num;
lean_object* v_b_4202_ = stack[3].m_obj;
lean_object* v___y_4203_ = stack[4].m_obj;
lean_object* v_res_4216_;
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_as_4199_, v_i_4200_, v_stop_4201_, v_b_4202_, v___y_4203_);
stack->m_obj
 = v_res_4216_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0___boxed(lean_object* v_as_4217_, lean_object* v_i_4218_, lean_object* v_stop_4219_, lean_object* v_b_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
size_t v_i_boxed_4223_; size_t v_stop_boxed_4224_; lean_object* v_res_4225_; 
v_i_boxed_4223_ = lean_unbox_usize(v_i_4218_);
lean_dec(v_i_4218_);
v_stop_boxed_4224_ = lean_unbox_usize(v_stop_4219_);
lean_dec(v_stop_4219_);
v_res_4225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_as_4217_, v_i_boxed_4223_, v_stop_boxed_4224_, v_b_4220_, v___y_4221_);
lean_dec_ref(v_as_4217_);
return v_res_4225_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(lean_object* v_as_4226_, size_t v_i_4227_, size_t v_stop_4228_, lean_object* v_b_4229_, lean_object* v___y_4230_){
_start:
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_usize_dec_eq(v_i_4227_, v_stop_4228_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_array_uget_borrowed(v_as_4226_, v_i_4227_);
v___x_4234_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v___x_4233_, v___y_4230_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v_fst_4236_; lean_object* v_snd_4237_; size_t v___x_4238_; size_t v___x_4239_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v_fst_4236_ = lean_ctor_get(v_a_4235_, 0);
lean_inc(v_fst_4236_);
v_snd_4237_ = lean_ctor_get(v_a_4235_, 1);
lean_inc(v_snd_4237_);
lean_dec(v_a_4235_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_i_4227_, v___x_4238_);
v_i_4227_ = v___x_4239_;
v_b_4229_ = v_fst_4236_;
v___y_4230_ = v_snd_4237_;
goto _start;
}
else
{
return v___x_4234_;
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4241_, 0, v_b_4229_);
lean_ctor_set(v___x_4241_, 1, v___y_4230_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4226_ = stack[0].m_obj;
size_t v_i_4227_ = stack[1].m_num;
size_t v_stop_4228_ = stack[2].m_num;
lean_object* v_b_4229_ = stack[3].m_obj;
lean_object* v___y_4230_ = stack[4].m_obj;
lean_object* v_res_4243_;
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_as_4226_, v_i_4227_, v_stop_4228_, v_b_4229_, v___y_4230_);
stack->m_obj
 = v_res_4243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1___boxed(lean_object* v_as_4244_, lean_object* v_i_4245_, lean_object* v_stop_4246_, lean_object* v_b_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
size_t v_i_boxed_4250_; size_t v_stop_boxed_4251_; lean_object* v_res_4252_; 
v_i_boxed_4250_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_stop_boxed_4251_ = lean_unbox_usize(v_stop_4246_);
lean_dec(v_stop_4246_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_as_4244_, v_i_boxed_4250_, v_stop_boxed_4251_, v_b_4247_, v___y_4248_);
lean_dec_ref(v_as_4244_);
return v_res_4252_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(lean_object* v_as_4253_, size_t v_i_4254_, size_t v_stop_4255_, lean_object* v_b_4256_, lean_object* v___y_4257_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = lean_usize_dec_eq(v_i_4254_, v_stop_4255_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = lean_array_uget_borrowed(v_as_4253_, v_i_4254_);
v___x_4261_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v___x_4260_, v___y_4257_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v_fst_4263_; lean_object* v_snd_4264_; size_t v___x_4265_; size_t v___x_4266_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
v_fst_4263_ = lean_ctor_get(v_a_4262_, 0);
lean_inc(v_fst_4263_);
v_snd_4264_ = lean_ctor_get(v_a_4262_, 1);
lean_inc(v_snd_4264_);
lean_dec(v_a_4262_);
v___x_4265_ = ((size_t)1ULL);
v___x_4266_ = lean_usize_add(v_i_4254_, v___x_4265_);
v_i_4254_ = v___x_4266_;
v_b_4256_ = v_fst_4263_;
v___y_4257_ = v_snd_4264_;
goto _start;
}
else
{
return v___x_4261_;
}
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v_b_4256_);
lean_ctor_set(v___x_4268_, 1, v___y_4257_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4253_ = stack[0].m_obj;
size_t v_i_4254_ = stack[1].m_num;
size_t v_stop_4255_ = stack[2].m_num;
lean_object* v_b_4256_ = stack[3].m_obj;
lean_object* v___y_4257_ = stack[4].m_obj;
lean_object* v_res_4270_;
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_as_4253_, v_i_4254_, v_stop_4255_, v_b_4256_, v___y_4257_);
stack->m_obj
 = v_res_4270_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2___boxed(lean_object* v_as_4271_, lean_object* v_i_4272_, lean_object* v_stop_4273_, lean_object* v_b_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
size_t v_i_boxed_4277_; size_t v_stop_boxed_4278_; lean_object* v_res_4279_; 
v_i_boxed_4277_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_stop_boxed_4278_ = lean_unbox_usize(v_stop_4273_);
lean_dec(v_stop_4273_);
v_res_4279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_as_4271_, v_i_boxed_4277_, v_stop_boxed_4278_, v_b_4274_, v___y_4275_);
lean_dec_ref(v_as_4271_);
return v_res_4279_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(lean_object* v_data_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6));
v___x_4304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4291_, v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 1)
{
lean_object* v_val_4305_; 
v_val_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_val_4305_);
lean_dec_ref_known(v___x_4304_, 1);
if (lean_obj_tag(v_val_4305_) == 4)
{
lean_object* v_elems_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_elems_4306_ = lean_ctor_get(v_val_4305_, 0);
lean_inc_ref(v_elems_4306_);
lean_dec_ref_known(v_val_4305_, 1);
v___x_4307_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_4308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4291_, v___x_4307_);
if (lean_obj_tag(v___x_4308_) == 1)
{
lean_object* v_val_4309_; 
v_val_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_val_4309_);
lean_dec_ref_known(v___x_4308_, 1);
if (lean_obj_tag(v_val_4309_) == 4)
{
lean_object* v_elems_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_elems_4310_ = lean_ctor_get(v_val_4309_, 0);
lean_inc_ref(v_elems_4310_);
lean_dec_ref_known(v_val_4309_, 1);
v___x_4311_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7));
v___x_4312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4291_, v___x_4311_);
if (lean_obj_tag(v___x_4312_) == 1)
{
lean_object* v_val_4313_; 
v_val_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_val_4313_);
lean_dec_ref_known(v___x_4312_, 1);
if (lean_obj_tag(v_val_4313_) == 4)
{
lean_object* v_elems_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4369_; 
v_elems_4314_ = lean_ctor_get(v_val_4313_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_val_4313_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4316_ = v_val_4313_;
v_isShared_4317_ = v_isSharedCheck_4369_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_elems_4314_);
lean_dec(v_val_4313_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4369_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v_snd_4320_; lean_object* v___y_4340_; lean_object* v_snd_4344_; lean_object* v___y_4356_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4318_ = lean_unsigned_to_nat(0u);
v___x_4359_ = lean_array_get_size(v_elems_4306_);
v___x_4360_ = lean_nat_dec_lt(v___x_4318_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_dec_ref(v_elems_4306_);
v_snd_4344_ = v_a_4292_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_nat_dec_le(v___x_4359_, v___x_4359_);
if (v___x_4362_ == 0)
{
if (v___x_4360_ == 0)
{
lean_dec_ref(v_elems_4306_);
v_snd_4344_ = v_a_4292_;
goto v___jp_4343_;
}
else
{
size_t v___x_4363_; size_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = ((size_t)0ULL);
v___x_4364_ = lean_usize_of_nat(v___x_4359_);
v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4306_, v___x_4363_, v___x_4364_, v___x_4361_, v_a_4292_);
lean_dec_ref(v_elems_4306_);
v___y_4356_ = v___x_4365_;
goto v___jp_4355_;
}
}
else
{
size_t v___x_4366_; size_t v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = ((size_t)0ULL);
v___x_4367_ = lean_usize_of_nat(v___x_4359_);
v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4306_, v___x_4366_, v___x_4367_, v___x_4361_, v_a_4292_);
lean_dec_ref(v_elems_4306_);
v___y_4356_ = v___x_4368_;
goto v___jp_4355_;
}
}
v___jp_4319_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4321_ = lean_array_get_size(v_elems_4314_);
v___x_4322_ = lean_box(0);
v___x_4323_ = lean_nat_dec_lt(v___x_4318_, v___x_4321_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4326_; 
lean_dec_ref(v_elems_4314_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v_snd_4320_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4324_);
v___x_4326_ = v___x_4316_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
else
{
uint8_t v___x_4328_; 
v___x_4328_ = lean_nat_dec_le(v___x_4321_, v___x_4321_);
if (v___x_4328_ == 0)
{
if (v___x_4323_ == 0)
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
lean_dec_ref(v_elems_4314_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4322_);
lean_ctor_set(v___x_4329_, 1, v_snd_4320_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4329_);
v___x_4331_ = v___x_4316_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
else
{
size_t v___x_4333_; size_t v___x_4334_; lean_object* v___x_4335_; 
lean_del_object(v___x_4316_);
v___x_4333_ = ((size_t)0ULL);
v___x_4334_ = lean_usize_of_nat(v___x_4321_);
v___x_4335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4314_, v___x_4333_, v___x_4334_, v___x_4322_, v_snd_4320_);
lean_dec_ref(v_elems_4314_);
return v___x_4335_;
}
}
else
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
lean_del_object(v___x_4316_);
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = lean_usize_of_nat(v___x_4321_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4314_, v___x_4336_, v___x_4337_, v___x_4322_, v_snd_4320_);
lean_dec_ref(v_elems_4314_);
return v___x_4338_;
}
}
}
v___jp_4339_:
{
if (lean_obj_tag(v___y_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v_snd_4342_; 
v_a_4341_ = lean_ctor_get(v___y_4340_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___y_4340_, 1);
v_snd_4342_ = lean_ctor_get(v_a_4341_, 1);
lean_inc(v_snd_4342_);
lean_dec(v_a_4341_);
v_snd_4320_ = v_snd_4342_;
goto v___jp_4319_;
}
else
{
lean_del_object(v___x_4316_);
lean_dec_ref(v_elems_4314_);
return v___y_4340_;
}
}
v___jp_4343_:
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = lean_array_get_size(v_elems_4310_);
v___x_4346_ = lean_nat_dec_lt(v___x_4318_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_dec_ref(v_elems_4310_);
v_snd_4320_ = v_snd_4344_;
goto v___jp_4319_;
}
else
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = lean_box(0);
v___x_4348_ = lean_nat_dec_le(v___x_4345_, v___x_4345_);
if (v___x_4348_ == 0)
{
if (v___x_4346_ == 0)
{
lean_dec_ref(v_elems_4310_);
v_snd_4320_ = v_snd_4344_;
goto v___jp_4319_;
}
else
{
size_t v___x_4349_; size_t v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = ((size_t)0ULL);
v___x_4350_ = lean_usize_of_nat(v___x_4345_);
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4310_, v___x_4349_, v___x_4350_, v___x_4347_, v_snd_4344_);
lean_dec_ref(v_elems_4310_);
v___y_4340_ = v___x_4351_;
goto v___jp_4339_;
}
}
else
{
size_t v___x_4352_; size_t v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = ((size_t)0ULL);
v___x_4353_ = lean_usize_of_nat(v___x_4345_);
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4310_, v___x_4352_, v___x_4353_, v___x_4347_, v_snd_4344_);
lean_dec_ref(v_elems_4310_);
v___y_4340_ = v___x_4354_;
goto v___jp_4339_;
}
}
}
v___jp_4355_:
{
if (lean_obj_tag(v___y_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v_snd_4358_; 
v_a_4357_ = lean_ctor_get(v___y_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___y_4356_, 1);
v_snd_4358_ = lean_ctor_get(v_a_4357_, 1);
lean_inc(v_snd_4358_);
lean_dec(v_a_4357_);
v_snd_4344_ = v_snd_4358_;
goto v___jp_4343_;
}
else
{
lean_del_object(v___x_4316_);
lean_dec_ref(v_elems_4314_);
lean_dec_ref(v_elems_4310_);
return v___y_4356_;
}
}
}
}
else
{
lean_dec(v_val_4313_);
lean_dec_ref(v_elems_4310_);
lean_dec_ref(v_elems_4306_);
lean_dec_ref(v_a_4292_);
goto v___jp_4294_;
}
}
else
{
lean_dec(v___x_4312_);
lean_dec_ref(v_elems_4310_);
lean_dec_ref(v_elems_4306_);
lean_dec_ref(v_a_4292_);
goto v___jp_4294_;
}
}
else
{
lean_dec(v_val_4309_);
lean_dec_ref(v_elems_4306_);
lean_dec_ref(v_a_4292_);
goto v___jp_4297_;
}
}
else
{
lean_dec(v___x_4308_);
lean_dec_ref(v_elems_4306_);
lean_dec_ref(v_a_4292_);
goto v___jp_4297_;
}
}
else
{
lean_dec(v_val_4305_);
lean_dec_ref(v_a_4292_);
goto v___jp_4300_;
}
}
else
{
lean_dec(v___x_4304_);
lean_dec_ref(v_a_4292_);
goto v___jp_4300_;
}
v___jp_4294_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1));
v___x_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
v___jp_4297_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3));
v___x_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
v___jp_4300_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5));
v___x_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_4291_ = stack[0].m_obj;
lean_object* v_a_4292_ = stack[1].m_obj;
lean_object* v_res_4370_;
v_res_4370_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_data_4291_, v_a_4292_);
stack->m_obj
 = v_res_4370_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___boxed(lean_object* v_data_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_data_4371_, v_a_4372_);
lean_dec(v_data_4371_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(lean_object* v_init_4375_, lean_object* v_x_4376_){
_start:
{
if (lean_obj_tag(v_x_4376_) == 0)
{
lean_object* v_k_4377_; lean_object* v_v_4378_; lean_object* v_l_4379_; lean_object* v_r_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_k_4377_ = lean_ctor_get(v_x_4376_, 1);
v_v_4378_ = lean_ctor_get(v_x_4376_, 2);
v_l_4379_ = lean_ctor_get(v_x_4376_, 3);
v_r_4380_ = lean_ctor_get(v_x_4376_, 4);
v___x_4381_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v_init_4375_, v_r_4380_);
lean_inc(v_v_4378_);
lean_inc(v_k_4377_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_k_4377_);
lean_ctor_set(v___x_4382_, 1, v_v_4378_);
v___x_4383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v___x_4381_);
v_init_4375_ = v___x_4383_;
v_x_4376_ = v_l_4379_;
goto _start;
}
else
{
return v_init_4375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3___boxed(lean_object* v_init_4385_, lean_object* v_x_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v_init_4385_, v_x_4386_);
lean_dec(v_x_4386_);
return v_res_4387_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(lean_object* v_m_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_buckets_4390_; lean_object* v___x_4391_; uint64_t v___x_4392_; uint64_t v___x_4393_; uint64_t v___x_4394_; uint64_t v_fold_4395_; uint64_t v___x_4396_; uint64_t v___x_4397_; uint64_t v___x_4398_; size_t v___x_4399_; size_t v___x_4400_; size_t v___x_4401_; size_t v___x_4402_; size_t v___x_4403_; lean_object* v___x_4404_; uint8_t v___x_4405_; 
v_buckets_4390_ = lean_ctor_get(v_m_4388_, 1);
v___x_4391_ = lean_array_get_size(v_buckets_4390_);
v___x_4392_ = lean_uint64_of_nat(v_a_4389_);
v___x_4393_ = 32ULL;
v___x_4394_ = lean_uint64_shift_right(v___x_4392_, v___x_4393_);
v_fold_4395_ = lean_uint64_xor(v___x_4392_, v___x_4394_);
v___x_4396_ = 16ULL;
v___x_4397_ = lean_uint64_shift_right(v_fold_4395_, v___x_4396_);
v___x_4398_ = lean_uint64_xor(v_fold_4395_, v___x_4397_);
v___x_4399_ = lean_uint64_to_usize(v___x_4398_);
v___x_4400_ = lean_usize_of_nat(v___x_4391_);
v___x_4401_ = ((size_t)1ULL);
v___x_4402_ = lean_usize_sub(v___x_4400_, v___x_4401_);
v___x_4403_ = lean_usize_land(v___x_4399_, v___x_4402_);
v___x_4404_ = lean_array_uget_borrowed(v_buckets_4390_, v___x_4403_);
v___x_4405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_4389_, v___x_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4388_ = stack[0].m_obj;
lean_object* v_a_4389_ = stack[1].m_obj;
uint8_t v_res_4406_;
v_res_4406_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_m_4388_, v_a_4389_);
stack->m_num = v_res_4406_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg___boxed(lean_object* v_m_4407_, lean_object* v_a_4408_){
_start:
{
uint8_t v_res_4409_; lean_object* v_r_4410_; 
v_res_4409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_m_4407_, v_a_4408_);
lean_dec(v_a_4408_);
lean_dec_ref(v_m_4407_);
v_r_4410_ = lean_box(v_res_4409_);
return v_r_4410_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(lean_object* v_x_4412_, lean_object* v_x_4413_){
_start:
{
if (lean_obj_tag(v_x_4413_) == 0)
{
return v_x_4412_;
}
else
{
lean_object* v_head_4414_; lean_object* v_tail_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v_head_4414_ = lean_ctor_get(v_x_4413_, 0);
v_tail_4415_ = lean_ctor_get(v_x_4413_, 1);
v___x_4416_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0));
v___x_4417_ = lean_string_append(v_x_4412_, v___x_4416_);
v___x_4418_ = lean_string_append(v___x_4417_, v_head_4414_);
v_x_4412_ = v___x_4418_;
v_x_4413_ = v_tail_4415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___boxed(lean_object* v_x_4420_, lean_object* v_x_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v_x_4420_, v_x_4421_);
lean_dec(v_x_4421_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object* v_x_4426_){
_start:
{
if (lean_obj_tag(v_x_4426_) == 0)
{
lean_object* v___x_4427_; 
v___x_4427_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0));
return v___x_4427_;
}
else
{
lean_object* v_tail_4428_; 
v_tail_4428_ = lean_ctor_get(v_x_4426_, 1);
if (lean_obj_tag(v_tail_4428_) == 0)
{
lean_object* v_head_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_head_4429_ = lean_ctor_get(v_x_4426_, 0);
v___x_4430_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4431_ = lean_string_append(v___x_4430_, v_head_4429_);
v___x_4432_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2));
v___x_4433_ = lean_string_append(v___x_4431_, v___x_4432_);
return v___x_4433_;
}
else
{
lean_object* v_head_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; uint32_t v___x_4438_; lean_object* v___x_4439_; 
v_head_4434_ = lean_ctor_get(v_x_4426_, 0);
v___x_4435_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4436_ = lean_string_append(v___x_4435_, v_head_4434_);
v___x_4437_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v___x_4436_, v_tail_4428_);
v___x_4438_ = 93;
v___x_4439_ = lean_string_push(v___x_4437_, v___x_4438_);
return v___x_4439_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___boxed(lean_object* v_x_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_x_4440_);
lean_dec(v_x_4440_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(lean_object* v_init_4442_, lean_object* v_x_4443_){
_start:
{
if (lean_obj_tag(v_x_4443_) == 0)
{
lean_object* v_k_4444_; lean_object* v_l_4445_; lean_object* v_r_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_k_4444_ = lean_ctor_get(v_x_4443_, 1);
v_l_4445_ = lean_ctor_get(v_x_4443_, 3);
v_r_4446_ = lean_ctor_get(v_x_4443_, 4);
v___x_4447_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4442_, v_r_4446_);
lean_inc(v_k_4444_);
v___x_4448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4448_, 0, v_k_4444_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
v_init_4442_ = v___x_4448_;
v_x_4443_ = v_l_4445_;
goto _start;
}
else
{
return v_init_4442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0___boxed(lean_object* v_init_4450_, lean_object* v_x_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4450_, v_x_4451_);
lean_dec(v_x_4451_);
return v_res_4452_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(lean_object* v_line_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_LeanExport_Json_parse(v_line_4478_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref(v_a_4479_);
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4492_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4492_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4486_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0));
v___x_4487_ = lean_string_append(v___x_4486_, v_a_4482_);
lean_dec(v_a_4482_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set_tag(v___x_4484_, 18);
lean_ctor_set(v___x_4484_, 0, v___x_4487_);
v___x_4489_ = v___x_4484_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_5586_; 
v_a_4493_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_4495_ = v___x_4481_;
v_isShared_4496_ = v_isSharedCheck_5586_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4481_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_5586_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
if (lean_obj_tag(v_a_4493_) == 5)
{
lean_object* v_kvPairs_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_5581_; 
v_kvPairs_4497_ = lean_ctor_get(v_a_4493_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_a_4493_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_4499_ = v_a_4493_;
v_isShared_4500_ = v_isSharedCheck_5581_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_kvPairs_4497_);
lean_dec(v_a_4493_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_5581_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v_fst_4514_; lean_object* v_snd_4515_; lean_object* v_tail_4516_; lean_object* v___y_5548_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5553_ = lean_box(0);
v___x_5554_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__3(v___x_5553_, v_kvPairs_4497_);
if (lean_obj_tag(v___x_5554_) == 1)
{
lean_object* v_tail_5555_; 
v_tail_5555_ = lean_ctor_get(v___x_5554_, 1);
lean_inc(v_tail_5555_);
if (lean_obj_tag(v_tail_5555_) == 1)
{
lean_object* v_head_5556_; lean_object* v_head_5557_; lean_object* v_tail_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5579_; 
v_head_5556_ = lean_ctor_get(v_tail_5555_, 0);
lean_inc(v_head_5556_);
v_head_5557_ = lean_ctor_get(v___x_5554_, 0);
v_tail_5558_ = lean_ctor_get(v_tail_5555_, 1);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_tail_5555_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; 
v_unused_5580_ = lean_ctor_get(v_tail_5555_, 0);
lean_dec(v_unused_5580_);
v___x_5560_ = v_tail_5555_;
v_isShared_5561_ = v_isSharedCheck_5579_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_tail_5558_);
lean_dec(v_tail_5555_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5579_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v_fst_5562_; lean_object* v_snd_5563_; lean_object* v___x_5564_; uint8_t v___x_5565_; 
v_fst_5562_ = lean_ctor_get(v_head_5556_, 0);
lean_inc(v_fst_5562_);
v_snd_5563_ = lean_ctor_get(v_head_5556_, 1);
lean_inc(v_snd_5563_);
lean_dec(v_head_5556_);
v___x_5564_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_5565_ = lean_string_dec_eq(v_fst_5562_, v___x_5564_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; uint8_t v___x_5567_; 
v___x_5566_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_5567_ = lean_string_dec_eq(v_fst_5562_, v___x_5566_);
if (v___x_5567_ == 0)
{
lean_object* v___x_5568_; uint8_t v___x_5569_; 
v___x_5568_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_5569_ = lean_string_dec_eq(v_fst_5562_, v___x_5568_);
lean_dec(v_fst_5562_);
if (v___x_5569_ == 0)
{
lean_dec(v_snd_5563_);
lean_del_object(v___x_5560_);
lean_dec(v_tail_5558_);
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
else
{
if (lean_obj_tag(v_tail_5558_) == 0)
{
lean_object* v___x_5571_; 
lean_inc(v_head_5557_);
lean_dec_ref_known(v___x_5554_, 2);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 0, v_head_5557_);
v___x_5571_ = v___x_5560_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_head_5557_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_tail_5558_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
v_fst_4514_ = v___x_5568_;
v_snd_4515_ = v_snd_5563_;
v_tail_4516_ = v___x_5571_;
goto v___jp_4513_;
}
}
else
{
lean_dec(v_snd_5563_);
lean_del_object(v___x_5560_);
lean_dec(v_tail_5558_);
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
}
}
else
{
lean_dec(v_fst_5562_);
if (lean_obj_tag(v_tail_5558_) == 0)
{
lean_object* v___x_5574_; 
lean_inc(v_head_5557_);
lean_dec_ref_known(v___x_5554_, 2);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 0, v_head_5557_);
v___x_5574_ = v___x_5560_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_head_5557_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v_tail_5558_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
v_fst_4514_ = v___x_5566_;
v_snd_4515_ = v_snd_5563_;
v_tail_4516_ = v___x_5574_;
goto v___jp_4513_;
}
}
else
{
lean_dec(v_snd_5563_);
lean_del_object(v___x_5560_);
lean_dec(v_tail_5558_);
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
}
}
else
{
lean_dec(v_fst_5562_);
if (lean_obj_tag(v_tail_5558_) == 0)
{
lean_object* v___x_5577_; 
lean_inc(v_head_5557_);
lean_dec_ref_known(v___x_5554_, 2);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 0, v_head_5557_);
v___x_5577_ = v___x_5560_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_head_5557_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_tail_5558_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
v_fst_4514_ = v___x_5564_;
v_snd_4515_ = v_snd_5563_;
v_tail_4516_ = v___x_5577_;
goto v___jp_4513_;
}
}
else
{
lean_dec(v_snd_5563_);
lean_del_object(v___x_5560_);
lean_dec(v_tail_5558_);
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
}
}
}
else
{
lean_dec(v_tail_5555_);
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
}
else
{
v___y_5548_ = v___x_5554_;
goto v___jp_5547_;
}
v___jp_4501_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4502_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0));
v___x_4503_ = lean_box(0);
v___x_4504_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v___x_4503_, v_kvPairs_4497_);
lean_dec(v_kvPairs_4497_);
v___x_4505_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v___x_4504_);
lean_dec(v___x_4504_);
v___x_4506_ = lean_string_append(v___x_4502_, v___x_4505_);
lean_dec_ref(v___x_4505_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set_tag(v___x_4499_, 18);
lean_ctor_set(v___x_4499_, 0, v___x_4506_);
v___x_4508_ = v___x_4499_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4508_);
v___x_4510_ = v___x_4495_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
v___jp_4513_:
{
lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4517_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_4518_ = lean_string_dec_eq(v_fst_4514_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_4520_ = lean_string_dec_eq(v_fst_4514_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4521_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_4522_ = lean_string_dec_eq(v_fst_4514_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; uint8_t v___x_4524_; 
v___x_4523_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4));
v___x_4524_ = lean_string_dec_eq(v_fst_4514_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5));
v___x_4526_ = lean_string_dec_eq(v_fst_4514_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6));
v___x_4528_ = lean_string_dec_eq(v_fst_4514_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_4530_ = lean_string_dec_eq(v_fst_4514_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4531_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7));
v___x_4532_ = lean_string_dec_eq(v_fst_4514_, v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8));
v___x_4534_ = lean_string_dec_eq(v_fst_4514_, v___x_4533_);
lean_dec_ref(v_fst_4514_);
if (v___x_4534_ == 0)
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4535_; lean_object* v___x_4536_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4535_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4535_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4536_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_kvPairs_4535_, v_a_4479_);
lean_dec(v_kvPairs_4535_);
return v___x_4536_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4537_; lean_object* v___x_4538_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4537_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4537_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4538_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_kvPairs_4537_, v_a_4479_);
lean_dec(v_kvPairs_4537_);
return v___x_4538_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4539_; lean_object* v___x_4540_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4539_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4539_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4540_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_kvPairs_4539_, v_a_4479_);
lean_dec(v_kvPairs_4539_);
return v___x_4540_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4541_; lean_object* v___x_4542_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4541_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4541_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4542_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_kvPairs_4541_, v_a_4479_);
lean_dec(v_kvPairs_4541_);
return v___x_4542_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4543_; lean_object* v___x_4544_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4543_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4543_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4544_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_kvPairs_4543_, v_a_4479_);
lean_dec(v_kvPairs_4543_);
return v___x_4544_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 5)
{
if (lean_obj_tag(v_tail_4516_) == 0)
{
lean_object* v_kvPairs_4545_; lean_object* v___x_4546_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v_kvPairs_4545_ = lean_ctor_get(v_snd_4515_, 0);
lean_inc(v_kvPairs_4545_);
lean_dec_ref_known(v_snd_4515_, 1);
v___x_4546_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_kvPairs_4545_, v_a_4479_);
lean_dec(v_kvPairs_4545_);
return v___x_4546_;
}
else
{
lean_dec_ref_known(v_snd_4515_, 1);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 2)
{
lean_object* v_n_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_5178_; 
v_n_4547_ = lean_ctor_get(v_snd_4515_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v_snd_4515_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_4549_ = v_snd_4515_;
v_isShared_4550_ = v_isSharedCheck_5178_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_n_4547_);
lean_dec(v_snd_4515_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_5178_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v_mantissa_4551_; lean_object* v_exponent_4552_; lean_object* v_natZero_4553_; lean_object* v_intZero_4554_; uint8_t v_isNeg_4555_; 
v_mantissa_4551_ = lean_ctor_get(v_n_4547_, 0);
lean_inc(v_mantissa_4551_);
v_exponent_4552_ = lean_ctor_get(v_n_4547_, 1);
lean_inc(v_exponent_4552_);
lean_dec_ref(v_n_4547_);
v_natZero_4553_ = lean_unsigned_to_nat(0u);
v_intZero_4554_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4555_ = lean_int_dec_lt(v_mantissa_4551_, v_intZero_4554_);
if (v_isNeg_4555_ == 0)
{
uint8_t v___x_4556_; 
v___x_4556_ = lean_nat_dec_eq(v_exponent_4552_, v_natZero_4553_);
lean_dec(v_exponent_4552_);
if (v___x_4556_ == 0)
{
lean_dec(v_mantissa_4551_);
lean_del_object(v___x_4549_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_4516_) == 1)
{
lean_object* v_head_4557_; lean_object* v_tail_4558_; lean_object* v_fst_4559_; lean_object* v_snd_4560_; lean_object* v_a_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_head_4557_ = lean_ctor_get(v_tail_4516_, 0);
lean_inc(v_head_4557_);
v_tail_4558_ = lean_ctor_get(v_tail_4516_, 1);
lean_inc(v_tail_4558_);
lean_dec_ref_known(v_tail_4516_, 2);
v_fst_4559_ = lean_ctor_get(v_head_4557_, 0);
lean_inc(v_fst_4559_);
v_snd_4560_ = lean_ctor_get(v_head_4557_, 1);
lean_inc(v_snd_4560_);
lean_dec(v_head_4557_);
v_a_4561_ = lean_nat_abs(v_mantissa_4551_);
lean_dec(v_mantissa_4551_);
v___x_4562_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9));
v___x_4563_ = lean_string_dec_eq(v_fst_4559_, v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10));
v___x_4565_ = lean_string_dec_eq(v_fst_4559_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; uint8_t v___x_4567_; 
v___x_4566_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11));
v___x_4567_ = lean_string_dec_eq(v_fst_4559_, v___x_4566_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4568_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12));
v___x_4569_ = lean_string_dec_eq(v_fst_4559_, v___x_4568_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4570_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13));
v___x_4571_ = lean_string_dec_eq(v_fst_4559_, v___x_4570_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; uint8_t v___x_4573_; 
v___x_4572_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14));
v___x_4573_ = lean_string_dec_eq(v_fst_4559_, v___x_4572_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; uint8_t v___x_4575_; 
v___x_4574_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15));
v___x_4575_ = lean_string_dec_eq(v_fst_4559_, v___x_4574_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16));
v___x_4577_ = lean_string_dec_eq(v_fst_4559_, v___x_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17));
v___x_4579_ = lean_string_dec_eq(v_fst_4559_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; uint8_t v___x_4581_; 
v___x_4580_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18));
v___x_4581_ = lean_string_dec_eq(v_fst_4559_, v___x_4580_);
if (v___x_4581_ == 0)
{
lean_object* v___x_4582_; uint8_t v___x_4583_; 
v___x_4582_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19));
v___x_4583_ = lean_string_dec_eq(v_fst_4559_, v___x_4582_);
lean_dec(v_fst_4559_);
if (v___x_4583_ == 0)
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4584_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4584_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4629_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4587_ = v___x_4584_;
v_isShared_4588_ = v_isSharedCheck_4629_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4584_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4629_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v_snd_4589_; lean_object* v_fst_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4628_; 
v_snd_4589_ = lean_ctor_get(v_a_4585_, 1);
v_fst_4590_ = lean_ctor_get(v_a_4585_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_a_4585_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4592_ = v_a_4585_;
v_isShared_4593_ = v_isSharedCheck_4628_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_snd_4589_);
lean_inc(v_fst_4590_);
lean_dec(v_a_4585_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4628_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v_stream_4594_; lean_object* v_nameMap_4595_; lean_object* v_levelMap_4596_; lean_object* v_exprMap_4597_; lean_object* v_recursorRuleMap_4598_; lean_object* v_constMap_4599_; lean_object* v_constOrder_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4627_; 
v_stream_4594_ = lean_ctor_get(v_snd_4589_, 0);
v_nameMap_4595_ = lean_ctor_get(v_snd_4589_, 1);
v_levelMap_4596_ = lean_ctor_get(v_snd_4589_, 2);
v_exprMap_4597_ = lean_ctor_get(v_snd_4589_, 3);
v_recursorRuleMap_4598_ = lean_ctor_get(v_snd_4589_, 4);
v_constMap_4599_ = lean_ctor_get(v_snd_4589_, 5);
v_constOrder_4600_ = lean_ctor_get(v_snd_4589_, 6);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_snd_4589_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4602_ = v_snd_4589_;
v_isShared_4603_ = v_isSharedCheck_4627_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_constOrder_4600_);
lean_inc(v_constMap_4599_);
lean_inc(v_recursorRuleMap_4598_);
lean_inc(v_exprMap_4597_);
lean_inc(v_levelMap_4596_);
lean_inc(v_nameMap_4595_);
lean_inc(v_stream_4594_);
lean_dec(v_snd_4589_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4627_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
uint8_t v___x_4604_; 
v___x_4604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4597_, v_a_4561_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4608_; 
lean_del_object(v___x_4549_);
v___x_4605_ = lean_box(0);
v___x_4606_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4597_, v_a_4561_, v_fst_4590_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 3, v___x_4606_);
v___x_4608_ = v___x_4602_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_stream_4594_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_nameMap_4595_);
lean_ctor_set(v_reuseFailAlloc_4615_, 2, v_levelMap_4596_);
lean_ctor_set(v_reuseFailAlloc_4615_, 3, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4615_, 4, v_recursorRuleMap_4598_);
lean_ctor_set(v_reuseFailAlloc_4615_, 5, v_constMap_4599_);
lean_ctor_set(v_reuseFailAlloc_4615_, 6, v_constOrder_4600_);
v___x_4608_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4610_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 1, v___x_4608_);
lean_ctor_set(v___x_4592_, 0, v___x_4605_);
v___x_4610_ = v___x_4592_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4614_, 1, v___x_4608_);
v___x_4610_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4612_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 0, v___x_4610_);
v___x_4612_ = v___x_4587_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
lean_del_object(v___x_4602_);
lean_dec_ref(v_constOrder_4600_);
lean_dec_ref(v_constMap_4599_);
lean_dec_ref(v_recursorRuleMap_4598_);
lean_dec_ref(v_exprMap_4597_);
lean_dec_ref(v_levelMap_4596_);
lean_dec_ref(v_nameMap_4595_);
lean_dec_ref(v_stream_4594_);
lean_del_object(v___x_4592_);
lean_dec(v_fst_4590_);
v___x_4616_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4617_ = l_Nat_reprFast(v_a_4561_);
v___x_4618_ = lean_string_append(v___x_4616_, v___x_4617_);
lean_dec_ref(v___x_4617_);
v___x_4619_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4620_ = lean_string_append(v___x_4618_, v___x_4619_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4620_);
v___x_4622_ = v___x_4549_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4624_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set_tag(v___x_4587_, 1);
lean_ctor_set(v___x_4587_, 0, v___x_4622_);
v___x_4624_ = v___x_4587_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4630_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4584_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4584_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4638_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4638_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_snd_4560_, v_a_4479_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4683_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4683_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4683_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_snd_4643_; lean_object* v_fst_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4682_; 
v_snd_4643_ = lean_ctor_get(v_a_4639_, 1);
v_fst_4644_ = lean_ctor_get(v_a_4639_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_a_4639_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4646_ = v_a_4639_;
v_isShared_4647_ = v_isSharedCheck_4682_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_snd_4643_);
lean_inc(v_fst_4644_);
lean_dec(v_a_4639_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4682_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v_stream_4648_; lean_object* v_nameMap_4649_; lean_object* v_levelMap_4650_; lean_object* v_exprMap_4651_; lean_object* v_recursorRuleMap_4652_; lean_object* v_constMap_4653_; lean_object* v_constOrder_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4681_; 
v_stream_4648_ = lean_ctor_get(v_snd_4643_, 0);
v_nameMap_4649_ = lean_ctor_get(v_snd_4643_, 1);
v_levelMap_4650_ = lean_ctor_get(v_snd_4643_, 2);
v_exprMap_4651_ = lean_ctor_get(v_snd_4643_, 3);
v_recursorRuleMap_4652_ = lean_ctor_get(v_snd_4643_, 4);
v_constMap_4653_ = lean_ctor_get(v_snd_4643_, 5);
v_constOrder_4654_ = lean_ctor_get(v_snd_4643_, 6);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_snd_4643_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4656_ = v_snd_4643_;
v_isShared_4657_ = v_isSharedCheck_4681_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_constOrder_4654_);
lean_inc(v_constMap_4653_);
lean_inc(v_recursorRuleMap_4652_);
lean_inc(v_exprMap_4651_);
lean_inc(v_levelMap_4650_);
lean_inc(v_nameMap_4649_);
lean_inc(v_stream_4648_);
lean_dec(v_snd_4643_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4681_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
uint8_t v___x_4658_; 
v___x_4658_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4651_, v_a_4561_);
if (v___x_4658_ == 0)
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_del_object(v___x_4549_);
v___x_4659_ = lean_box(0);
v___x_4660_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4651_, v_a_4561_, v_fst_4644_);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 3, v___x_4660_);
v___x_4662_ = v___x_4656_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_stream_4648_);
lean_ctor_set(v_reuseFailAlloc_4669_, 1, v_nameMap_4649_);
lean_ctor_set(v_reuseFailAlloc_4669_, 2, v_levelMap_4650_);
lean_ctor_set(v_reuseFailAlloc_4669_, 3, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4669_, 4, v_recursorRuleMap_4652_);
lean_ctor_set(v_reuseFailAlloc_4669_, 5, v_constMap_4653_);
lean_ctor_set(v_reuseFailAlloc_4669_, 6, v_constOrder_4654_);
v___x_4662_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4664_; 
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 1, v___x_4662_);
lean_ctor_set(v___x_4646_, 0, v___x_4659_);
v___x_4664_ = v___x_4646_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4659_);
lean_ctor_set(v_reuseFailAlloc_4668_, 1, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
lean_object* v___x_4666_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4664_);
v___x_4666_ = v___x_4641_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
}
else
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
lean_del_object(v___x_4656_);
lean_dec_ref(v_constOrder_4654_);
lean_dec_ref(v_constMap_4653_);
lean_dec_ref(v_recursorRuleMap_4652_);
lean_dec_ref(v_exprMap_4651_);
lean_dec_ref(v_levelMap_4650_);
lean_dec_ref(v_nameMap_4649_);
lean_dec_ref(v_stream_4648_);
lean_del_object(v___x_4646_);
lean_dec(v_fst_4644_);
v___x_4670_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4671_ = l_Nat_reprFast(v_a_4561_);
v___x_4672_ = lean_string_append(v___x_4670_, v___x_4671_);
lean_dec_ref(v___x_4671_);
v___x_4673_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4674_ = lean_string_append(v___x_4672_, v___x_4673_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4674_);
v___x_4676_ = v___x_4549_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4674_);
v___x_4676_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4678_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set_tag(v___x_4641_, 1);
lean_ctor_set(v___x_4641_, 0, v___x_4676_);
v___x_4678_ = v___x_4641_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4684_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4638_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4638_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4692_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4692_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_snd_4560_, v_a_4479_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4737_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4737_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4737_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v_snd_4697_; lean_object* v_fst_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4736_; 
v_snd_4697_ = lean_ctor_get(v_a_4693_, 1);
v_fst_4698_ = lean_ctor_get(v_a_4693_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v_a_4693_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4700_ = v_a_4693_;
v_isShared_4701_ = v_isSharedCheck_4736_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_snd_4697_);
lean_inc(v_fst_4698_);
lean_dec(v_a_4693_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4736_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_stream_4702_; lean_object* v_nameMap_4703_; lean_object* v_levelMap_4704_; lean_object* v_exprMap_4705_; lean_object* v_recursorRuleMap_4706_; lean_object* v_constMap_4707_; lean_object* v_constOrder_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4735_; 
v_stream_4702_ = lean_ctor_get(v_snd_4697_, 0);
v_nameMap_4703_ = lean_ctor_get(v_snd_4697_, 1);
v_levelMap_4704_ = lean_ctor_get(v_snd_4697_, 2);
v_exprMap_4705_ = lean_ctor_get(v_snd_4697_, 3);
v_recursorRuleMap_4706_ = lean_ctor_get(v_snd_4697_, 4);
v_constMap_4707_ = lean_ctor_get(v_snd_4697_, 5);
v_constOrder_4708_ = lean_ctor_get(v_snd_4697_, 6);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_snd_4697_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4710_ = v_snd_4697_;
v_isShared_4711_ = v_isSharedCheck_4735_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_constOrder_4708_);
lean_inc(v_constMap_4707_);
lean_inc(v_recursorRuleMap_4706_);
lean_inc(v_exprMap_4705_);
lean_inc(v_levelMap_4704_);
lean_inc(v_nameMap_4703_);
lean_inc(v_stream_4702_);
lean_dec(v_snd_4697_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4735_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
uint8_t v___x_4712_; 
v___x_4712_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4705_, v_a_4561_);
if (v___x_4712_ == 0)
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
lean_del_object(v___x_4549_);
v___x_4713_ = lean_box(0);
v___x_4714_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4705_, v_a_4561_, v_fst_4698_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 3, v___x_4714_);
v___x_4716_ = v___x_4710_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_stream_4702_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_nameMap_4703_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_levelMap_4704_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_recursorRuleMap_4706_);
lean_ctor_set(v_reuseFailAlloc_4723_, 5, v_constMap_4707_);
lean_ctor_set(v_reuseFailAlloc_4723_, 6, v_constOrder_4708_);
v___x_4716_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4718_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 1, v___x_4716_);
lean_ctor_set(v___x_4700_, 0, v___x_4713_);
v___x_4718_ = v___x_4700_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; 
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 0, v___x_4718_);
v___x_4720_ = v___x_4695_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4718_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
else
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
lean_del_object(v___x_4710_);
lean_dec_ref(v_constOrder_4708_);
lean_dec_ref(v_constMap_4707_);
lean_dec_ref(v_recursorRuleMap_4706_);
lean_dec_ref(v_exprMap_4705_);
lean_dec_ref(v_levelMap_4704_);
lean_dec_ref(v_nameMap_4703_);
lean_dec_ref(v_stream_4702_);
lean_del_object(v___x_4700_);
lean_dec(v_fst_4698_);
v___x_4724_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4725_ = l_Nat_reprFast(v_a_4561_);
v___x_4726_ = lean_string_append(v___x_4724_, v___x_4725_);
lean_dec_ref(v___x_4725_);
v___x_4727_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4728_ = lean_string_append(v___x_4726_, v___x_4727_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4728_);
v___x_4730_ = v___x_4549_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
lean_object* v___x_4732_; 
if (v_isShared_4696_ == 0)
{
lean_ctor_set_tag(v___x_4695_, 1);
lean_ctor_set(v___x_4695_, 0, v___x_4730_);
v___x_4732_ = v___x_4695_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4738_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4692_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4692_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4746_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4746_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4791_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4749_ = v___x_4746_;
v_isShared_4750_ = v_isSharedCheck_4791_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4746_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4791_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_snd_4751_; lean_object* v_fst_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4790_; 
v_snd_4751_ = lean_ctor_get(v_a_4747_, 1);
v_fst_4752_ = lean_ctor_get(v_a_4747_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_a_4747_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4754_ = v_a_4747_;
v_isShared_4755_ = v_isSharedCheck_4790_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_snd_4751_);
lean_inc(v_fst_4752_);
lean_dec(v_a_4747_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4790_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v_stream_4756_; lean_object* v_nameMap_4757_; lean_object* v_levelMap_4758_; lean_object* v_exprMap_4759_; lean_object* v_recursorRuleMap_4760_; lean_object* v_constMap_4761_; lean_object* v_constOrder_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4789_; 
v_stream_4756_ = lean_ctor_get(v_snd_4751_, 0);
v_nameMap_4757_ = lean_ctor_get(v_snd_4751_, 1);
v_levelMap_4758_ = lean_ctor_get(v_snd_4751_, 2);
v_exprMap_4759_ = lean_ctor_get(v_snd_4751_, 3);
v_recursorRuleMap_4760_ = lean_ctor_get(v_snd_4751_, 4);
v_constMap_4761_ = lean_ctor_get(v_snd_4751_, 5);
v_constOrder_4762_ = lean_ctor_get(v_snd_4751_, 6);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_snd_4751_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4764_ = v_snd_4751_;
v_isShared_4765_ = v_isSharedCheck_4789_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_constOrder_4762_);
lean_inc(v_constMap_4761_);
lean_inc(v_recursorRuleMap_4760_);
lean_inc(v_exprMap_4759_);
lean_inc(v_levelMap_4758_);
lean_inc(v_nameMap_4757_);
lean_inc(v_stream_4756_);
lean_dec(v_snd_4751_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4789_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
uint8_t v___x_4766_; 
v___x_4766_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4759_, v_a_4561_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4770_; 
lean_del_object(v___x_4549_);
v___x_4767_ = lean_box(0);
v___x_4768_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4759_, v_a_4561_, v_fst_4752_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 3, v___x_4768_);
v___x_4770_ = v___x_4764_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_stream_4756_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_nameMap_4757_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_levelMap_4758_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_recursorRuleMap_4760_);
lean_ctor_set(v_reuseFailAlloc_4777_, 5, v_constMap_4761_);
lean_ctor_set(v_reuseFailAlloc_4777_, 6, v_constOrder_4762_);
v___x_4770_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4772_; 
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 1, v___x_4770_);
lean_ctor_set(v___x_4754_, 0, v___x_4767_);
v___x_4772_ = v___x_4754_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4767_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
lean_object* v___x_4774_; 
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4772_);
v___x_4774_ = v___x_4749_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
else
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4784_; 
lean_del_object(v___x_4764_);
lean_dec_ref(v_constOrder_4762_);
lean_dec_ref(v_constMap_4761_);
lean_dec_ref(v_recursorRuleMap_4760_);
lean_dec_ref(v_exprMap_4759_);
lean_dec_ref(v_levelMap_4758_);
lean_dec_ref(v_nameMap_4757_);
lean_dec_ref(v_stream_4756_);
lean_del_object(v___x_4754_);
lean_dec(v_fst_4752_);
v___x_4778_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4779_ = l_Nat_reprFast(v_a_4561_);
v___x_4780_ = lean_string_append(v___x_4778_, v___x_4779_);
lean_dec_ref(v___x_4779_);
v___x_4781_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4782_ = lean_string_append(v___x_4780_, v___x_4781_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4782_);
v___x_4784_ = v___x_4549_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4782_);
v___x_4784_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4786_; 
if (v_isShared_4750_ == 0)
{
lean_ctor_set_tag(v___x_4749_, 1);
lean_ctor_set(v___x_4749_, 0, v___x_4784_);
v___x_4786_ = v___x_4749_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4792_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4746_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4746_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4800_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4800_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4845_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4803_ = v___x_4800_;
v_isShared_4804_ = v_isSharedCheck_4845_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4845_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_snd_4805_; lean_object* v_fst_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4844_; 
v_snd_4805_ = lean_ctor_get(v_a_4801_, 1);
v_fst_4806_ = lean_ctor_get(v_a_4801_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v_a_4801_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4808_ = v_a_4801_;
v_isShared_4809_ = v_isSharedCheck_4844_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_snd_4805_);
lean_inc(v_fst_4806_);
lean_dec(v_a_4801_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4844_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_stream_4810_; lean_object* v_nameMap_4811_; lean_object* v_levelMap_4812_; lean_object* v_exprMap_4813_; lean_object* v_recursorRuleMap_4814_; lean_object* v_constMap_4815_; lean_object* v_constOrder_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4843_; 
v_stream_4810_ = lean_ctor_get(v_snd_4805_, 0);
v_nameMap_4811_ = lean_ctor_get(v_snd_4805_, 1);
v_levelMap_4812_ = lean_ctor_get(v_snd_4805_, 2);
v_exprMap_4813_ = lean_ctor_get(v_snd_4805_, 3);
v_recursorRuleMap_4814_ = lean_ctor_get(v_snd_4805_, 4);
v_constMap_4815_ = lean_ctor_get(v_snd_4805_, 5);
v_constOrder_4816_ = lean_ctor_get(v_snd_4805_, 6);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_snd_4805_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4818_ = v_snd_4805_;
v_isShared_4819_ = v_isSharedCheck_4843_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_constOrder_4816_);
lean_inc(v_constMap_4815_);
lean_inc(v_recursorRuleMap_4814_);
lean_inc(v_exprMap_4813_);
lean_inc(v_levelMap_4812_);
lean_inc(v_nameMap_4811_);
lean_inc(v_stream_4810_);
lean_dec(v_snd_4805_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4843_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
uint8_t v___x_4820_; 
v___x_4820_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4813_, v_a_4561_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
lean_del_object(v___x_4549_);
v___x_4821_ = lean_box(0);
v___x_4822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4813_, v_a_4561_, v_fst_4806_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 3, v___x_4822_);
v___x_4824_ = v___x_4818_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_stream_4810_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_nameMap_4811_);
lean_ctor_set(v_reuseFailAlloc_4831_, 2, v_levelMap_4812_);
lean_ctor_set(v_reuseFailAlloc_4831_, 3, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4831_, 4, v_recursorRuleMap_4814_);
lean_ctor_set(v_reuseFailAlloc_4831_, 5, v_constMap_4815_);
lean_ctor_set(v_reuseFailAlloc_4831_, 6, v_constOrder_4816_);
v___x_4824_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4826_; 
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 1, v___x_4824_);
lean_ctor_set(v___x_4808_, 0, v___x_4821_);
v___x_4826_ = v___x_4808_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v___x_4824_);
v___x_4826_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4828_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v___x_4826_);
v___x_4828_ = v___x_4803_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
lean_del_object(v___x_4818_);
lean_dec_ref(v_constOrder_4816_);
lean_dec_ref(v_constMap_4815_);
lean_dec_ref(v_recursorRuleMap_4814_);
lean_dec_ref(v_exprMap_4813_);
lean_dec_ref(v_levelMap_4812_);
lean_dec_ref(v_nameMap_4811_);
lean_dec_ref(v_stream_4810_);
lean_del_object(v___x_4808_);
lean_dec(v_fst_4806_);
v___x_4832_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4833_ = l_Nat_reprFast(v_a_4561_);
v___x_4834_ = lean_string_append(v___x_4832_, v___x_4833_);
lean_dec_ref(v___x_4833_);
v___x_4835_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4836_ = lean_string_append(v___x_4834_, v___x_4835_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4836_);
v___x_4838_ = v___x_4549_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4840_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 1);
lean_ctor_set(v___x_4803_, 0, v___x_4838_);
v___x_4840_ = v___x_4803_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4846_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4800_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4800_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4854_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4854_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4899_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4857_ = v___x_4854_;
v_isShared_4858_ = v_isSharedCheck_4899_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4854_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4899_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v_snd_4859_; lean_object* v_fst_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4898_; 
v_snd_4859_ = lean_ctor_get(v_a_4855_, 1);
v_fst_4860_ = lean_ctor_get(v_a_4855_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_a_4855_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4862_ = v_a_4855_;
v_isShared_4863_ = v_isSharedCheck_4898_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_snd_4859_);
lean_inc(v_fst_4860_);
lean_dec(v_a_4855_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4898_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v_stream_4864_; lean_object* v_nameMap_4865_; lean_object* v_levelMap_4866_; lean_object* v_exprMap_4867_; lean_object* v_recursorRuleMap_4868_; lean_object* v_constMap_4869_; lean_object* v_constOrder_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4897_; 
v_stream_4864_ = lean_ctor_get(v_snd_4859_, 0);
v_nameMap_4865_ = lean_ctor_get(v_snd_4859_, 1);
v_levelMap_4866_ = lean_ctor_get(v_snd_4859_, 2);
v_exprMap_4867_ = lean_ctor_get(v_snd_4859_, 3);
v_recursorRuleMap_4868_ = lean_ctor_get(v_snd_4859_, 4);
v_constMap_4869_ = lean_ctor_get(v_snd_4859_, 5);
v_constOrder_4870_ = lean_ctor_get(v_snd_4859_, 6);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_snd_4859_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4872_ = v_snd_4859_;
v_isShared_4873_ = v_isSharedCheck_4897_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_constOrder_4870_);
lean_inc(v_constMap_4869_);
lean_inc(v_recursorRuleMap_4868_);
lean_inc(v_exprMap_4867_);
lean_inc(v_levelMap_4866_);
lean_inc(v_nameMap_4865_);
lean_inc(v_stream_4864_);
lean_dec(v_snd_4859_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4897_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
uint8_t v___x_4874_; 
v___x_4874_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4867_, v_a_4561_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4878_; 
lean_del_object(v___x_4549_);
v___x_4875_ = lean_box(0);
v___x_4876_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4867_, v_a_4561_, v_fst_4860_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 3, v___x_4876_);
v___x_4878_ = v___x_4872_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_stream_4864_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_nameMap_4865_);
lean_ctor_set(v_reuseFailAlloc_4885_, 2, v_levelMap_4866_);
lean_ctor_set(v_reuseFailAlloc_4885_, 3, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4885_, 4, v_recursorRuleMap_4868_);
lean_ctor_set(v_reuseFailAlloc_4885_, 5, v_constMap_4869_);
lean_ctor_set(v_reuseFailAlloc_4885_, 6, v_constOrder_4870_);
v___x_4878_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4880_; 
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 1, v___x_4878_);
lean_ctor_set(v___x_4862_, 0, v___x_4875_);
v___x_4880_ = v___x_4862_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4875_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v___x_4878_);
v___x_4880_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
lean_object* v___x_4882_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4880_);
v___x_4882_ = v___x_4857_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
lean_del_object(v___x_4872_);
lean_dec_ref(v_constOrder_4870_);
lean_dec_ref(v_constMap_4869_);
lean_dec_ref(v_recursorRuleMap_4868_);
lean_dec_ref(v_exprMap_4867_);
lean_dec_ref(v_levelMap_4866_);
lean_dec_ref(v_nameMap_4865_);
lean_dec_ref(v_stream_4864_);
lean_del_object(v___x_4862_);
lean_dec(v_fst_4860_);
v___x_4886_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4887_ = l_Nat_reprFast(v_a_4561_);
v___x_4888_ = lean_string_append(v___x_4886_, v___x_4887_);
lean_dec_ref(v___x_4887_);
v___x_4889_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4890_ = lean_string_append(v___x_4888_, v___x_4889_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4890_);
v___x_4892_ = v___x_4549_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
lean_object* v___x_4894_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set_tag(v___x_4857_, 1);
lean_ctor_set(v___x_4857_, 0, v___x_4892_);
v___x_4894_ = v___x_4857_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4900_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4854_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4854_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4908_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4908_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4953_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4953_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4953_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v_snd_4913_; lean_object* v_fst_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4952_; 
v_snd_4913_ = lean_ctor_get(v_a_4909_, 1);
v_fst_4914_ = lean_ctor_get(v_a_4909_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_a_4909_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4916_ = v_a_4909_;
v_isShared_4917_ = v_isSharedCheck_4952_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_snd_4913_);
lean_inc(v_fst_4914_);
lean_dec(v_a_4909_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4952_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v_stream_4918_; lean_object* v_nameMap_4919_; lean_object* v_levelMap_4920_; lean_object* v_exprMap_4921_; lean_object* v_recursorRuleMap_4922_; lean_object* v_constMap_4923_; lean_object* v_constOrder_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4951_; 
v_stream_4918_ = lean_ctor_get(v_snd_4913_, 0);
v_nameMap_4919_ = lean_ctor_get(v_snd_4913_, 1);
v_levelMap_4920_ = lean_ctor_get(v_snd_4913_, 2);
v_exprMap_4921_ = lean_ctor_get(v_snd_4913_, 3);
v_recursorRuleMap_4922_ = lean_ctor_get(v_snd_4913_, 4);
v_constMap_4923_ = lean_ctor_get(v_snd_4913_, 5);
v_constOrder_4924_ = lean_ctor_get(v_snd_4913_, 6);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_snd_4913_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4926_ = v_snd_4913_;
v_isShared_4927_ = v_isSharedCheck_4951_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_constOrder_4924_);
lean_inc(v_constMap_4923_);
lean_inc(v_recursorRuleMap_4922_);
lean_inc(v_exprMap_4921_);
lean_inc(v_levelMap_4920_);
lean_inc(v_nameMap_4919_);
lean_inc(v_stream_4918_);
lean_dec(v_snd_4913_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4951_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
uint8_t v___x_4928_; 
v___x_4928_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4921_, v_a_4561_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
lean_del_object(v___x_4549_);
v___x_4929_ = lean_box(0);
v___x_4930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4921_, v_a_4561_, v_fst_4914_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 3, v___x_4930_);
v___x_4932_ = v___x_4926_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_stream_4918_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_nameMap_4919_);
lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_levelMap_4920_);
lean_ctor_set(v_reuseFailAlloc_4939_, 3, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4939_, 4, v_recursorRuleMap_4922_);
lean_ctor_set(v_reuseFailAlloc_4939_, 5, v_constMap_4923_);
lean_ctor_set(v_reuseFailAlloc_4939_, 6, v_constOrder_4924_);
v___x_4932_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4934_; 
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 1, v___x_4932_);
lean_ctor_set(v___x_4916_, 0, v___x_4929_);
v___x_4934_ = v___x_4916_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
lean_object* v___x_4936_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4934_);
v___x_4936_ = v___x_4911_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
else
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
lean_del_object(v___x_4926_);
lean_dec_ref(v_constOrder_4924_);
lean_dec_ref(v_constMap_4923_);
lean_dec_ref(v_recursorRuleMap_4922_);
lean_dec_ref(v_exprMap_4921_);
lean_dec_ref(v_levelMap_4920_);
lean_dec_ref(v_nameMap_4919_);
lean_dec_ref(v_stream_4918_);
lean_del_object(v___x_4916_);
lean_dec(v_fst_4914_);
v___x_4940_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4941_ = l_Nat_reprFast(v_a_4561_);
v___x_4942_ = lean_string_append(v___x_4940_, v___x_4941_);
lean_dec_ref(v___x_4941_);
v___x_4943_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4944_ = lean_string_append(v___x_4942_, v___x_4943_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4944_);
v___x_4946_ = v___x_4549_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4948_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set_tag(v___x_4911_, 1);
lean_ctor_set(v___x_4911_, 0, v___x_4946_);
v___x_4948_ = v___x_4911_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_4954_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4908_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4908_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_4962_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_4962_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_5007_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_4965_ = v___x_4962_;
v_isShared_4966_ = v_isSharedCheck_5007_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4962_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_5007_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v_snd_4967_; lean_object* v_fst_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_5006_; 
v_snd_4967_ = lean_ctor_get(v_a_4963_, 1);
v_fst_4968_ = lean_ctor_get(v_a_4963_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v_a_4963_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4970_ = v_a_4963_;
v_isShared_4971_ = v_isSharedCheck_5006_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_snd_4967_);
lean_inc(v_fst_4968_);
lean_dec(v_a_4963_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_5006_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v_stream_4972_; lean_object* v_nameMap_4973_; lean_object* v_levelMap_4974_; lean_object* v_exprMap_4975_; lean_object* v_recursorRuleMap_4976_; lean_object* v_constMap_4977_; lean_object* v_constOrder_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5005_; 
v_stream_4972_ = lean_ctor_get(v_snd_4967_, 0);
v_nameMap_4973_ = lean_ctor_get(v_snd_4967_, 1);
v_levelMap_4974_ = lean_ctor_get(v_snd_4967_, 2);
v_exprMap_4975_ = lean_ctor_get(v_snd_4967_, 3);
v_recursorRuleMap_4976_ = lean_ctor_get(v_snd_4967_, 4);
v_constMap_4977_ = lean_ctor_get(v_snd_4967_, 5);
v_constOrder_4978_ = lean_ctor_get(v_snd_4967_, 6);
v_isSharedCheck_5005_ = !lean_is_exclusive(v_snd_4967_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4980_ = v_snd_4967_;
v_isShared_4981_ = v_isSharedCheck_5005_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_constOrder_4978_);
lean_inc(v_constMap_4977_);
lean_inc(v_recursorRuleMap_4976_);
lean_inc(v_exprMap_4975_);
lean_inc(v_levelMap_4974_);
lean_inc(v_nameMap_4973_);
lean_inc(v_stream_4972_);
lean_dec(v_snd_4967_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5005_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
uint8_t v___x_4982_; 
v___x_4982_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_4975_, v_a_4561_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4986_; 
lean_del_object(v___x_4549_);
v___x_4983_ = lean_box(0);
v___x_4984_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4975_, v_a_4561_, v_fst_4968_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 3, v___x_4984_);
v___x_4986_ = v___x_4980_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_stream_4972_);
lean_ctor_set(v_reuseFailAlloc_4993_, 1, v_nameMap_4973_);
lean_ctor_set(v_reuseFailAlloc_4993_, 2, v_levelMap_4974_);
lean_ctor_set(v_reuseFailAlloc_4993_, 3, v___x_4984_);
lean_ctor_set(v_reuseFailAlloc_4993_, 4, v_recursorRuleMap_4976_);
lean_ctor_set(v_reuseFailAlloc_4993_, 5, v_constMap_4977_);
lean_ctor_set(v_reuseFailAlloc_4993_, 6, v_constOrder_4978_);
v___x_4986_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4988_; 
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 1, v___x_4986_);
lean_ctor_set(v___x_4970_, 0, v___x_4983_);
v___x_4988_ = v___x_4970_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4983_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4990_; 
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 0, v___x_4988_);
v___x_4990_ = v___x_4965_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
else
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_5000_; 
lean_del_object(v___x_4980_);
lean_dec_ref(v_constOrder_4978_);
lean_dec_ref(v_constMap_4977_);
lean_dec_ref(v_recursorRuleMap_4976_);
lean_dec_ref(v_exprMap_4975_);
lean_dec_ref(v_levelMap_4974_);
lean_dec_ref(v_nameMap_4973_);
lean_dec_ref(v_stream_4972_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4968_);
v___x_4994_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_4995_ = l_Nat_reprFast(v_a_4561_);
v___x_4996_ = lean_string_append(v___x_4994_, v___x_4995_);
lean_dec_ref(v___x_4995_);
v___x_4997_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_4998_ = lean_string_append(v___x_4996_, v___x_4997_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_4998_);
v___x_5000_ = v___x_4549_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5004_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
lean_object* v___x_5002_; 
if (v_isShared_4966_ == 0)
{
lean_ctor_set_tag(v___x_4965_, 1);
lean_ctor_set(v___x_4965_, 0, v___x_5000_);
v___x_5002_ = v___x_4965_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_5008_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4962_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4962_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_5016_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5016_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_snd_4560_, v_a_4479_);
lean_dec(v_snd_4560_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5061_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5019_ = v___x_5016_;
v_isShared_5020_ = v_isSharedCheck_5061_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5061_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v_snd_5021_; lean_object* v_fst_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5060_; 
v_snd_5021_ = lean_ctor_get(v_a_5017_, 1);
v_fst_5022_ = lean_ctor_get(v_a_5017_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v_a_5017_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5024_ = v_a_5017_;
v_isShared_5025_ = v_isSharedCheck_5060_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_snd_5021_);
lean_inc(v_fst_5022_);
lean_dec(v_a_5017_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5060_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v_stream_5026_; lean_object* v_nameMap_5027_; lean_object* v_levelMap_5028_; lean_object* v_exprMap_5029_; lean_object* v_recursorRuleMap_5030_; lean_object* v_constMap_5031_; lean_object* v_constOrder_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5059_; 
v_stream_5026_ = lean_ctor_get(v_snd_5021_, 0);
v_nameMap_5027_ = lean_ctor_get(v_snd_5021_, 1);
v_levelMap_5028_ = lean_ctor_get(v_snd_5021_, 2);
v_exprMap_5029_ = lean_ctor_get(v_snd_5021_, 3);
v_recursorRuleMap_5030_ = lean_ctor_get(v_snd_5021_, 4);
v_constMap_5031_ = lean_ctor_get(v_snd_5021_, 5);
v_constOrder_5032_ = lean_ctor_get(v_snd_5021_, 6);
v_isSharedCheck_5059_ = !lean_is_exclusive(v_snd_5021_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5034_ = v_snd_5021_;
v_isShared_5035_ = v_isSharedCheck_5059_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_constOrder_5032_);
lean_inc(v_constMap_5031_);
lean_inc(v_recursorRuleMap_5030_);
lean_inc(v_exprMap_5029_);
lean_inc(v_levelMap_5028_);
lean_inc(v_nameMap_5027_);
lean_inc(v_stream_5026_);
lean_dec(v_snd_5021_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5059_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
uint8_t v___x_5036_; 
v___x_5036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_5029_, v_a_4561_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5040_; 
lean_del_object(v___x_4549_);
v___x_5037_ = lean_box(0);
v___x_5038_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_5029_, v_a_4561_, v_fst_5022_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 3, v___x_5038_);
v___x_5040_ = v___x_5034_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_stream_5026_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v_nameMap_5027_);
lean_ctor_set(v_reuseFailAlloc_5047_, 2, v_levelMap_5028_);
lean_ctor_set(v_reuseFailAlloc_5047_, 3, v___x_5038_);
lean_ctor_set(v_reuseFailAlloc_5047_, 4, v_recursorRuleMap_5030_);
lean_ctor_set(v_reuseFailAlloc_5047_, 5, v_constMap_5031_);
lean_ctor_set(v_reuseFailAlloc_5047_, 6, v_constOrder_5032_);
v___x_5040_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
lean_object* v___x_5042_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v___x_5040_);
lean_ctor_set(v___x_5024_, 0, v___x_5037_);
v___x_5042_ = v___x_5024_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5044_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5042_);
v___x_5044_ = v___x_5019_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5042_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
else
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5054_; 
lean_del_object(v___x_5034_);
lean_dec_ref(v_constOrder_5032_);
lean_dec_ref(v_constMap_5031_);
lean_dec_ref(v_recursorRuleMap_5030_);
lean_dec_ref(v_exprMap_5029_);
lean_dec_ref(v_levelMap_5028_);
lean_dec_ref(v_nameMap_5027_);
lean_dec_ref(v_stream_5026_);
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
v___x_5048_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_5049_ = l_Nat_reprFast(v_a_4561_);
v___x_5050_ = lean_string_append(v___x_5048_, v___x_5049_);
lean_dec_ref(v___x_5049_);
v___x_5051_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5052_ = lean_string_append(v___x_5050_, v___x_5051_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_5052_);
v___x_5054_ = v___x_4549_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
lean_object* v___x_5056_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set_tag(v___x_5019_, 1);
lean_ctor_set(v___x_5019_, 0, v___x_5054_);
v___x_5056_ = v___x_5019_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5054_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5069_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_5062_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5064_ = v___x_5016_;
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5016_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_5070_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5070_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_snd_4560_, v_a_4479_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5115_; 
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5073_ = v___x_5070_;
v_isShared_5074_ = v_isSharedCheck_5115_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5070_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5115_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v_snd_5075_; lean_object* v_fst_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5114_; 
v_snd_5075_ = lean_ctor_get(v_a_5071_, 1);
v_fst_5076_ = lean_ctor_get(v_a_5071_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v_a_5071_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5078_ = v_a_5071_;
v_isShared_5079_ = v_isSharedCheck_5114_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_snd_5075_);
lean_inc(v_fst_5076_);
lean_dec(v_a_5071_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5114_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v_stream_5080_; lean_object* v_nameMap_5081_; lean_object* v_levelMap_5082_; lean_object* v_exprMap_5083_; lean_object* v_recursorRuleMap_5084_; lean_object* v_constMap_5085_; lean_object* v_constOrder_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5113_; 
v_stream_5080_ = lean_ctor_get(v_snd_5075_, 0);
v_nameMap_5081_ = lean_ctor_get(v_snd_5075_, 1);
v_levelMap_5082_ = lean_ctor_get(v_snd_5075_, 2);
v_exprMap_5083_ = lean_ctor_get(v_snd_5075_, 3);
v_recursorRuleMap_5084_ = lean_ctor_get(v_snd_5075_, 4);
v_constMap_5085_ = lean_ctor_get(v_snd_5075_, 5);
v_constOrder_5086_ = lean_ctor_get(v_snd_5075_, 6);
v_isSharedCheck_5113_ = !lean_is_exclusive(v_snd_5075_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5088_ = v_snd_5075_;
v_isShared_5089_ = v_isSharedCheck_5113_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_constOrder_5086_);
lean_inc(v_constMap_5085_);
lean_inc(v_recursorRuleMap_5084_);
lean_inc(v_exprMap_5083_);
lean_inc(v_levelMap_5082_);
lean_inc(v_nameMap_5081_);
lean_inc(v_stream_5080_);
lean_dec(v_snd_5075_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5113_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
uint8_t v___x_5090_; 
v___x_5090_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_5083_, v_a_4561_);
if (v___x_5090_ == 0)
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
lean_del_object(v___x_4549_);
v___x_5091_ = lean_box(0);
v___x_5092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_5083_, v_a_4561_, v_fst_5076_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 3, v___x_5092_);
v___x_5094_ = v___x_5088_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_stream_5080_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_nameMap_5081_);
lean_ctor_set(v_reuseFailAlloc_5101_, 2, v_levelMap_5082_);
lean_ctor_set(v_reuseFailAlloc_5101_, 3, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5101_, 4, v_recursorRuleMap_5084_);
lean_ctor_set(v_reuseFailAlloc_5101_, 5, v_constMap_5085_);
lean_ctor_set(v_reuseFailAlloc_5101_, 6, v_constOrder_5086_);
v___x_5094_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5096_; 
if (v_isShared_5079_ == 0)
{
lean_ctor_set(v___x_5078_, 1, v___x_5094_);
lean_ctor_set(v___x_5078_, 0, v___x_5091_);
v___x_5096_ = v___x_5078_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5091_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5098_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5096_);
v___x_5098_ = v___x_5073_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
lean_del_object(v___x_5088_);
lean_dec_ref(v_constOrder_5086_);
lean_dec_ref(v_constMap_5085_);
lean_dec_ref(v_recursorRuleMap_5084_);
lean_dec_ref(v_exprMap_5083_);
lean_dec_ref(v_levelMap_5082_);
lean_dec_ref(v_nameMap_5081_);
lean_dec_ref(v_stream_5080_);
lean_del_object(v___x_5078_);
lean_dec(v_fst_5076_);
v___x_5102_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_5103_ = l_Nat_reprFast(v_a_4561_);
v___x_5104_ = lean_string_append(v___x_5102_, v___x_5103_);
lean_dec_ref(v___x_5103_);
v___x_5105_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5106_ = lean_string_append(v___x_5104_, v___x_5105_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_5106_);
v___x_5108_ = v___x_4549_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5110_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set_tag(v___x_5073_, 1);
lean_ctor_set(v___x_5073_, 0, v___x_5108_);
v___x_5110_ = v___x_5073_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
return v___x_5110_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_5116_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5070_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5070_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_4559_);
if (lean_obj_tag(v_tail_4558_) == 0)
{
lean_object* v___x_5124_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5124_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_snd_4560_, v_a_4479_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5169_; 
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5127_ = v___x_5124_;
v_isShared_5128_ = v_isSharedCheck_5169_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5124_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5169_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v_snd_5129_; lean_object* v_fst_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5168_; 
v_snd_5129_ = lean_ctor_get(v_a_5125_, 1);
v_fst_5130_ = lean_ctor_get(v_a_5125_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_a_5125_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5132_ = v_a_5125_;
v_isShared_5133_ = v_isSharedCheck_5168_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_snd_5129_);
lean_inc(v_fst_5130_);
lean_dec(v_a_5125_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5168_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v_stream_5134_; lean_object* v_nameMap_5135_; lean_object* v_levelMap_5136_; lean_object* v_exprMap_5137_; lean_object* v_recursorRuleMap_5138_; lean_object* v_constMap_5139_; lean_object* v_constOrder_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5167_; 
v_stream_5134_ = lean_ctor_get(v_snd_5129_, 0);
v_nameMap_5135_ = lean_ctor_get(v_snd_5129_, 1);
v_levelMap_5136_ = lean_ctor_get(v_snd_5129_, 2);
v_exprMap_5137_ = lean_ctor_get(v_snd_5129_, 3);
v_recursorRuleMap_5138_ = lean_ctor_get(v_snd_5129_, 4);
v_constMap_5139_ = lean_ctor_get(v_snd_5129_, 5);
v_constOrder_5140_ = lean_ctor_get(v_snd_5129_, 6);
v_isSharedCheck_5167_ = !lean_is_exclusive(v_snd_5129_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5142_ = v_snd_5129_;
v_isShared_5143_ = v_isSharedCheck_5167_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_constOrder_5140_);
lean_inc(v_constMap_5139_);
lean_inc(v_recursorRuleMap_5138_);
lean_inc(v_exprMap_5137_);
lean_inc(v_levelMap_5136_);
lean_inc(v_nameMap_5135_);
lean_inc(v_stream_5134_);
lean_dec(v_snd_5129_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5167_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
uint8_t v___x_5144_; 
v___x_5144_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_exprMap_5137_, v_a_4561_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5148_; 
lean_del_object(v___x_4549_);
v___x_5145_ = lean_box(0);
v___x_5146_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_5137_, v_a_4561_, v_fst_5130_);
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 3, v___x_5146_);
v___x_5148_ = v___x_5142_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_stream_5134_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v_nameMap_5135_);
lean_ctor_set(v_reuseFailAlloc_5155_, 2, v_levelMap_5136_);
lean_ctor_set(v_reuseFailAlloc_5155_, 3, v___x_5146_);
lean_ctor_set(v_reuseFailAlloc_5155_, 4, v_recursorRuleMap_5138_);
lean_ctor_set(v_reuseFailAlloc_5155_, 5, v_constMap_5139_);
lean_ctor_set(v_reuseFailAlloc_5155_, 6, v_constOrder_5140_);
v___x_5148_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5150_; 
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 1, v___x_5148_);
lean_ctor_set(v___x_5132_, 0, v___x_5145_);
v___x_5150_ = v___x_5132_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5145_);
lean_ctor_set(v_reuseFailAlloc_5154_, 1, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5152_; 
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 0, v___x_5150_);
v___x_5152_ = v___x_5127_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5150_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5162_; 
lean_del_object(v___x_5142_);
lean_dec_ref(v_constOrder_5140_);
lean_dec_ref(v_constMap_5139_);
lean_dec_ref(v_recursorRuleMap_5138_);
lean_dec_ref(v_exprMap_5137_);
lean_dec_ref(v_levelMap_5136_);
lean_dec_ref(v_nameMap_5135_);
lean_dec_ref(v_stream_5134_);
lean_del_object(v___x_5132_);
lean_dec(v_fst_5130_);
v___x_5156_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___closed__0));
v___x_5157_ = l_Nat_reprFast(v_a_4561_);
v___x_5158_ = lean_string_append(v___x_5156_, v___x_5157_);
lean_dec_ref(v___x_5157_);
v___x_5159_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5160_ = lean_string_append(v___x_5158_, v___x_5159_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set_tag(v___x_4549_, 18);
lean_ctor_set(v___x_4549_, 0, v___x_5160_);
v___x_5162_ = v___x_4549_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5160_);
v___x_5162_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
lean_object* v___x_5164_; 
if (v_isShared_5128_ == 0)
{
lean_ctor_set_tag(v___x_5127_, 1);
lean_ctor_set(v___x_5127_, 0, v___x_5162_);
v___x_5164_ = v___x_5127_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5162_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
lean_dec(v_a_4561_);
lean_del_object(v___x_4549_);
v_a_5170_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5124_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_5124_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
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
lean_dec(v_a_4561_);
lean_dec(v_snd_4560_);
lean_dec(v_tail_4558_);
lean_del_object(v___x_4549_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_mantissa_4551_);
lean_del_object(v___x_4549_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_exponent_4552_);
lean_dec(v_mantissa_4551_);
lean_del_object(v___x_4549_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 2)
{
lean_object* v_n_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5418_; 
v_n_5179_ = lean_ctor_get(v_snd_4515_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v_snd_4515_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5181_ = v_snd_4515_;
v_isShared_5182_ = v_isSharedCheck_5418_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_n_5179_);
lean_dec(v_snd_4515_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5418_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v_mantissa_5183_; lean_object* v_exponent_5184_; lean_object* v_natZero_5185_; lean_object* v_intZero_5186_; uint8_t v_isNeg_5187_; 
v_mantissa_5183_ = lean_ctor_get(v_n_5179_, 0);
lean_inc(v_mantissa_5183_);
v_exponent_5184_ = lean_ctor_get(v_n_5179_, 1);
lean_inc(v_exponent_5184_);
lean_dec_ref(v_n_5179_);
v_natZero_5185_ = lean_unsigned_to_nat(0u);
v_intZero_5186_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5187_ = lean_int_dec_lt(v_mantissa_5183_, v_intZero_5186_);
if (v_isNeg_5187_ == 0)
{
uint8_t v___x_5188_; 
v___x_5188_ = lean_nat_dec_eq(v_exponent_5184_, v_natZero_5185_);
lean_dec(v_exponent_5184_);
if (v___x_5188_ == 0)
{
lean_dec(v_mantissa_5183_);
lean_del_object(v___x_5181_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_4516_) == 1)
{
lean_object* v_head_5189_; lean_object* v_tail_5190_; lean_object* v_fst_5191_; lean_object* v_snd_5192_; lean_object* v_a_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; 
v_head_5189_ = lean_ctor_get(v_tail_4516_, 0);
lean_inc(v_head_5189_);
v_tail_5190_ = lean_ctor_get(v_tail_4516_, 1);
lean_inc(v_tail_5190_);
lean_dec_ref_known(v_tail_4516_, 2);
v_fst_5191_ = lean_ctor_get(v_head_5189_, 0);
lean_inc(v_fst_5191_);
v_snd_5192_ = lean_ctor_get(v_head_5189_, 1);
lean_inc(v_snd_5192_);
lean_dec(v_head_5189_);
v_a_5193_ = lean_nat_abs(v_mantissa_5183_);
lean_dec(v_mantissa_5183_);
v___x_5194_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20));
v___x_5195_ = lean_string_dec_eq(v_fst_5191_, v___x_5194_);
if (v___x_5195_ == 0)
{
lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5196_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21));
v___x_5197_ = lean_string_dec_eq(v_fst_5191_, v___x_5196_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; uint8_t v___x_5199_; 
v___x_5198_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22));
v___x_5199_ = lean_string_dec_eq(v_fst_5191_, v___x_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; uint8_t v___x_5201_; 
v___x_5200_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23));
v___x_5201_ = lean_string_dec_eq(v_fst_5191_, v___x_5200_);
lean_dec(v_fst_5191_);
if (v___x_5201_ == 0)
{
lean_dec(v_a_5193_);
lean_dec(v_snd_5192_);
lean_dec(v_tail_5190_);
lean_del_object(v___x_5181_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_5190_) == 0)
{
lean_object* v___x_5202_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5202_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_snd_5192_, v_a_4479_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5247_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5205_ = v___x_5202_;
v_isShared_5206_ = v_isSharedCheck_5247_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5202_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5247_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v_snd_5207_; lean_object* v_fst_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5246_; 
v_snd_5207_ = lean_ctor_get(v_a_5203_, 1);
v_fst_5208_ = lean_ctor_get(v_a_5203_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v_a_5203_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5210_ = v_a_5203_;
v_isShared_5211_ = v_isSharedCheck_5246_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_snd_5207_);
lean_inc(v_fst_5208_);
lean_dec(v_a_5203_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5246_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v_stream_5212_; lean_object* v_nameMap_5213_; lean_object* v_levelMap_5214_; lean_object* v_exprMap_5215_; lean_object* v_recursorRuleMap_5216_; lean_object* v_constMap_5217_; lean_object* v_constOrder_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5245_; 
v_stream_5212_ = lean_ctor_get(v_snd_5207_, 0);
v_nameMap_5213_ = lean_ctor_get(v_snd_5207_, 1);
v_levelMap_5214_ = lean_ctor_get(v_snd_5207_, 2);
v_exprMap_5215_ = lean_ctor_get(v_snd_5207_, 3);
v_recursorRuleMap_5216_ = lean_ctor_get(v_snd_5207_, 4);
v_constMap_5217_ = lean_ctor_get(v_snd_5207_, 5);
v_constOrder_5218_ = lean_ctor_get(v_snd_5207_, 6);
v_isSharedCheck_5245_ = !lean_is_exclusive(v_snd_5207_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5220_ = v_snd_5207_;
v_isShared_5221_ = v_isSharedCheck_5245_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_constOrder_5218_);
lean_inc(v_constMap_5217_);
lean_inc(v_recursorRuleMap_5216_);
lean_inc(v_exprMap_5215_);
lean_inc(v_levelMap_5214_);
lean_inc(v_nameMap_5213_);
lean_inc(v_stream_5212_);
lean_dec(v_snd_5207_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5245_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
uint8_t v___x_5222_; 
v___x_5222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5214_, v_a_5193_);
if (v___x_5222_ == 0)
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5226_; 
lean_del_object(v___x_5181_);
v___x_5223_ = lean_box(0);
v___x_5224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5214_, v_a_5193_, v_fst_5208_);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 2, v___x_5224_);
v___x_5226_ = v___x_5220_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_stream_5212_);
lean_ctor_set(v_reuseFailAlloc_5233_, 1, v_nameMap_5213_);
lean_ctor_set(v_reuseFailAlloc_5233_, 2, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5233_, 3, v_exprMap_5215_);
lean_ctor_set(v_reuseFailAlloc_5233_, 4, v_recursorRuleMap_5216_);
lean_ctor_set(v_reuseFailAlloc_5233_, 5, v_constMap_5217_);
lean_ctor_set(v_reuseFailAlloc_5233_, 6, v_constOrder_5218_);
v___x_5226_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5228_; 
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 1, v___x_5226_);
lean_ctor_set(v___x_5210_, 0, v___x_5223_);
v___x_5228_ = v___x_5210_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v___x_5226_);
v___x_5228_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
lean_object* v___x_5230_; 
if (v_isShared_5206_ == 0)
{
lean_ctor_set(v___x_5205_, 0, v___x_5228_);
v___x_5230_ = v___x_5205_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5228_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5240_; 
lean_del_object(v___x_5220_);
lean_dec_ref(v_constOrder_5218_);
lean_dec_ref(v_constMap_5217_);
lean_dec_ref(v_recursorRuleMap_5216_);
lean_dec_ref(v_exprMap_5215_);
lean_dec_ref(v_levelMap_5214_);
lean_dec_ref(v_nameMap_5213_);
lean_dec_ref(v_stream_5212_);
lean_del_object(v___x_5210_);
lean_dec(v_fst_5208_);
v___x_5234_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5235_ = l_Nat_reprFast(v_a_5193_);
v___x_5236_ = lean_string_append(v___x_5234_, v___x_5235_);
lean_dec_ref(v___x_5235_);
v___x_5237_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5238_ = lean_string_append(v___x_5236_, v___x_5237_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 18);
lean_ctor_set(v___x_5181_, 0, v___x_5238_);
v___x_5240_ = v___x_5181_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
lean_object* v___x_5242_; 
if (v_isShared_5206_ == 0)
{
lean_ctor_set_tag(v___x_5205_, 1);
lean_ctor_set(v___x_5205_, 0, v___x_5240_);
v___x_5242_ = v___x_5205_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5240_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec(v_a_5193_);
lean_del_object(v___x_5181_);
v_a_5248_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5202_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5202_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
else
{
lean_dec(v_a_5193_);
lean_dec(v_snd_5192_);
lean_dec(v_tail_5190_);
lean_del_object(v___x_5181_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_5191_);
if (lean_obj_tag(v_tail_5190_) == 0)
{
lean_object* v___x_5256_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5256_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_snd_5192_, v_a_4479_);
lean_dec(v_snd_5192_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5301_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5259_ = v___x_5256_;
v_isShared_5260_ = v_isSharedCheck_5301_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5256_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5301_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v_snd_5261_; lean_object* v_fst_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5300_; 
v_snd_5261_ = lean_ctor_get(v_a_5257_, 1);
v_fst_5262_ = lean_ctor_get(v_a_5257_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_a_5257_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5264_ = v_a_5257_;
v_isShared_5265_ = v_isSharedCheck_5300_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_snd_5261_);
lean_inc(v_fst_5262_);
lean_dec(v_a_5257_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5300_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v_stream_5266_; lean_object* v_nameMap_5267_; lean_object* v_levelMap_5268_; lean_object* v_exprMap_5269_; lean_object* v_recursorRuleMap_5270_; lean_object* v_constMap_5271_; lean_object* v_constOrder_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5299_; 
v_stream_5266_ = lean_ctor_get(v_snd_5261_, 0);
v_nameMap_5267_ = lean_ctor_get(v_snd_5261_, 1);
v_levelMap_5268_ = lean_ctor_get(v_snd_5261_, 2);
v_exprMap_5269_ = lean_ctor_get(v_snd_5261_, 3);
v_recursorRuleMap_5270_ = lean_ctor_get(v_snd_5261_, 4);
v_constMap_5271_ = lean_ctor_get(v_snd_5261_, 5);
v_constOrder_5272_ = lean_ctor_get(v_snd_5261_, 6);
v_isSharedCheck_5299_ = !lean_is_exclusive(v_snd_5261_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5274_ = v_snd_5261_;
v_isShared_5275_ = v_isSharedCheck_5299_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_constOrder_5272_);
lean_inc(v_constMap_5271_);
lean_inc(v_recursorRuleMap_5270_);
lean_inc(v_exprMap_5269_);
lean_inc(v_levelMap_5268_);
lean_inc(v_nameMap_5267_);
lean_inc(v_stream_5266_);
lean_dec(v_snd_5261_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5299_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
uint8_t v___x_5276_; 
v___x_5276_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5268_, v_a_5193_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5280_; 
lean_del_object(v___x_5181_);
v___x_5277_ = lean_box(0);
v___x_5278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5268_, v_a_5193_, v_fst_5262_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 2, v___x_5278_);
v___x_5280_ = v___x_5274_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_stream_5266_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_nameMap_5267_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v___x_5278_);
lean_ctor_set(v_reuseFailAlloc_5287_, 3, v_exprMap_5269_);
lean_ctor_set(v_reuseFailAlloc_5287_, 4, v_recursorRuleMap_5270_);
lean_ctor_set(v_reuseFailAlloc_5287_, 5, v_constMap_5271_);
lean_ctor_set(v_reuseFailAlloc_5287_, 6, v_constOrder_5272_);
v___x_5280_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
lean_object* v___x_5282_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 1, v___x_5280_);
lean_ctor_set(v___x_5264_, 0, v___x_5277_);
v___x_5282_ = v___x_5264_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5277_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
lean_object* v___x_5284_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5282_);
v___x_5284_ = v___x_5259_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
else
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5294_; 
lean_del_object(v___x_5274_);
lean_dec_ref(v_constOrder_5272_);
lean_dec_ref(v_constMap_5271_);
lean_dec_ref(v_recursorRuleMap_5270_);
lean_dec_ref(v_exprMap_5269_);
lean_dec_ref(v_levelMap_5268_);
lean_dec_ref(v_nameMap_5267_);
lean_dec_ref(v_stream_5266_);
lean_del_object(v___x_5264_);
lean_dec(v_fst_5262_);
v___x_5288_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5289_ = l_Nat_reprFast(v_a_5193_);
v___x_5290_ = lean_string_append(v___x_5288_, v___x_5289_);
lean_dec_ref(v___x_5289_);
v___x_5291_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5292_ = lean_string_append(v___x_5290_, v___x_5291_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 18);
lean_ctor_set(v___x_5181_, 0, v___x_5292_);
v___x_5294_ = v___x_5181_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5292_);
v___x_5294_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
lean_object* v___x_5296_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set_tag(v___x_5259_, 1);
lean_ctor_set(v___x_5259_, 0, v___x_5294_);
v___x_5296_ = v___x_5259_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec(v_a_5193_);
lean_del_object(v___x_5181_);
v_a_5302_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5256_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5256_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
else
{
lean_dec(v_a_5193_);
lean_dec(v_snd_5192_);
lean_dec(v_tail_5190_);
lean_del_object(v___x_5181_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_5191_);
if (lean_obj_tag(v_tail_5190_) == 0)
{
lean_object* v___x_5310_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5310_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_snd_5192_, v_a_4479_);
lean_dec(v_snd_5192_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5355_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5355_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5355_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v_snd_5315_; lean_object* v_fst_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5354_; 
v_snd_5315_ = lean_ctor_get(v_a_5311_, 1);
v_fst_5316_ = lean_ctor_get(v_a_5311_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_a_5311_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5318_ = v_a_5311_;
v_isShared_5319_ = v_isSharedCheck_5354_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_snd_5315_);
lean_inc(v_fst_5316_);
lean_dec(v_a_5311_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5354_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v_stream_5320_; lean_object* v_nameMap_5321_; lean_object* v_levelMap_5322_; lean_object* v_exprMap_5323_; lean_object* v_recursorRuleMap_5324_; lean_object* v_constMap_5325_; lean_object* v_constOrder_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5353_; 
v_stream_5320_ = lean_ctor_get(v_snd_5315_, 0);
v_nameMap_5321_ = lean_ctor_get(v_snd_5315_, 1);
v_levelMap_5322_ = lean_ctor_get(v_snd_5315_, 2);
v_exprMap_5323_ = lean_ctor_get(v_snd_5315_, 3);
v_recursorRuleMap_5324_ = lean_ctor_get(v_snd_5315_, 4);
v_constMap_5325_ = lean_ctor_get(v_snd_5315_, 5);
v_constOrder_5326_ = lean_ctor_get(v_snd_5315_, 6);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_snd_5315_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5328_ = v_snd_5315_;
v_isShared_5329_ = v_isSharedCheck_5353_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_constOrder_5326_);
lean_inc(v_constMap_5325_);
lean_inc(v_recursorRuleMap_5324_);
lean_inc(v_exprMap_5323_);
lean_inc(v_levelMap_5322_);
lean_inc(v_nameMap_5321_);
lean_inc(v_stream_5320_);
lean_dec(v_snd_5315_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5353_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
uint8_t v___x_5330_; 
v___x_5330_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5322_, v_a_5193_);
if (v___x_5330_ == 0)
{
lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5334_; 
lean_del_object(v___x_5181_);
v___x_5331_ = lean_box(0);
v___x_5332_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5322_, v_a_5193_, v_fst_5316_);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 2, v___x_5332_);
v___x_5334_ = v___x_5328_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_stream_5320_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_nameMap_5321_);
lean_ctor_set(v_reuseFailAlloc_5341_, 2, v___x_5332_);
lean_ctor_set(v_reuseFailAlloc_5341_, 3, v_exprMap_5323_);
lean_ctor_set(v_reuseFailAlloc_5341_, 4, v_recursorRuleMap_5324_);
lean_ctor_set(v_reuseFailAlloc_5341_, 5, v_constMap_5325_);
lean_ctor_set(v_reuseFailAlloc_5341_, 6, v_constOrder_5326_);
v___x_5334_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
lean_object* v___x_5336_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 1, v___x_5334_);
lean_ctor_set(v___x_5318_, 0, v___x_5331_);
v___x_5336_ = v___x_5318_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___x_5334_);
v___x_5336_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
lean_object* v___x_5338_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5336_);
v___x_5338_ = v___x_5313_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
else
{
lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
lean_del_object(v___x_5328_);
lean_dec_ref(v_constOrder_5326_);
lean_dec_ref(v_constMap_5325_);
lean_dec_ref(v_recursorRuleMap_5324_);
lean_dec_ref(v_exprMap_5323_);
lean_dec_ref(v_levelMap_5322_);
lean_dec_ref(v_nameMap_5321_);
lean_dec_ref(v_stream_5320_);
lean_del_object(v___x_5318_);
lean_dec(v_fst_5316_);
v___x_5342_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5343_ = l_Nat_reprFast(v_a_5193_);
v___x_5344_ = lean_string_append(v___x_5342_, v___x_5343_);
lean_dec_ref(v___x_5343_);
v___x_5345_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5346_ = lean_string_append(v___x_5344_, v___x_5345_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 18);
lean_ctor_set(v___x_5181_, 0, v___x_5346_);
v___x_5348_ = v___x_5181_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set_tag(v___x_5313_, 1);
lean_ctor_set(v___x_5313_, 0, v___x_5348_);
v___x_5350_ = v___x_5313_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
lean_dec(v_a_5193_);
lean_del_object(v___x_5181_);
v_a_5356_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5310_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5310_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
else
{
lean_dec(v_a_5193_);
lean_dec(v_snd_5192_);
lean_dec(v_tail_5190_);
lean_del_object(v___x_5181_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_5191_);
if (lean_obj_tag(v_tail_5190_) == 0)
{
lean_object* v___x_5364_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5364_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_snd_5192_, v_a_4479_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5409_; 
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5367_ = v___x_5364_;
v_isShared_5368_ = v_isSharedCheck_5409_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5364_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5409_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v_snd_5369_; lean_object* v_fst_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5408_; 
v_snd_5369_ = lean_ctor_get(v_a_5365_, 1);
v_fst_5370_ = lean_ctor_get(v_a_5365_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v_a_5365_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5372_ = v_a_5365_;
v_isShared_5373_ = v_isSharedCheck_5408_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_snd_5369_);
lean_inc(v_fst_5370_);
lean_dec(v_a_5365_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5408_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v_stream_5374_; lean_object* v_nameMap_5375_; lean_object* v_levelMap_5376_; lean_object* v_exprMap_5377_; lean_object* v_recursorRuleMap_5378_; lean_object* v_constMap_5379_; lean_object* v_constOrder_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5407_; 
v_stream_5374_ = lean_ctor_get(v_snd_5369_, 0);
v_nameMap_5375_ = lean_ctor_get(v_snd_5369_, 1);
v_levelMap_5376_ = lean_ctor_get(v_snd_5369_, 2);
v_exprMap_5377_ = lean_ctor_get(v_snd_5369_, 3);
v_recursorRuleMap_5378_ = lean_ctor_get(v_snd_5369_, 4);
v_constMap_5379_ = lean_ctor_get(v_snd_5369_, 5);
v_constOrder_5380_ = lean_ctor_get(v_snd_5369_, 6);
v_isSharedCheck_5407_ = !lean_is_exclusive(v_snd_5369_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5382_ = v_snd_5369_;
v_isShared_5383_ = v_isSharedCheck_5407_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_constOrder_5380_);
lean_inc(v_constMap_5379_);
lean_inc(v_recursorRuleMap_5378_);
lean_inc(v_exprMap_5377_);
lean_inc(v_levelMap_5376_);
lean_inc(v_nameMap_5375_);
lean_inc(v_stream_5374_);
lean_dec(v_snd_5369_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5407_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
uint8_t v___x_5384_; 
v___x_5384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_levelMap_5376_, v_a_5193_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5388_; 
lean_del_object(v___x_5181_);
v___x_5385_ = lean_box(0);
v___x_5386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5376_, v_a_5193_, v_fst_5370_);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 2, v___x_5386_);
v___x_5388_ = v___x_5382_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_stream_5374_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v_nameMap_5375_);
lean_ctor_set(v_reuseFailAlloc_5395_, 2, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5395_, 3, v_exprMap_5377_);
lean_ctor_set(v_reuseFailAlloc_5395_, 4, v_recursorRuleMap_5378_);
lean_ctor_set(v_reuseFailAlloc_5395_, 5, v_constMap_5379_);
lean_ctor_set(v_reuseFailAlloc_5395_, 6, v_constOrder_5380_);
v___x_5388_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5390_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5388_);
lean_ctor_set(v___x_5372_, 0, v___x_5385_);
v___x_5390_ = v___x_5372_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5385_);
lean_ctor_set(v_reuseFailAlloc_5394_, 1, v___x_5388_);
v___x_5390_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
lean_object* v___x_5392_; 
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v___x_5390_);
v___x_5392_ = v___x_5367_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5402_; 
lean_del_object(v___x_5382_);
lean_dec_ref(v_constOrder_5380_);
lean_dec_ref(v_constMap_5379_);
lean_dec_ref(v_recursorRuleMap_5378_);
lean_dec_ref(v_exprMap_5377_);
lean_dec_ref(v_levelMap_5376_);
lean_dec_ref(v_nameMap_5375_);
lean_dec_ref(v_stream_5374_);
lean_del_object(v___x_5372_);
lean_dec(v_fst_5370_);
v___x_5396_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___closed__0));
v___x_5397_ = l_Nat_reprFast(v_a_5193_);
v___x_5398_ = lean_string_append(v___x_5396_, v___x_5397_);
lean_dec_ref(v___x_5397_);
v___x_5399_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5400_ = lean_string_append(v___x_5398_, v___x_5399_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 18);
lean_ctor_set(v___x_5181_, 0, v___x_5400_);
v___x_5402_ = v___x_5181_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5400_);
v___x_5402_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
lean_object* v___x_5404_; 
if (v_isShared_5368_ == 0)
{
lean_ctor_set_tag(v___x_5367_, 1);
lean_ctor_set(v___x_5367_, 0, v___x_5402_);
v___x_5404_ = v___x_5367_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5417_; 
lean_dec(v_a_5193_);
lean_del_object(v___x_5181_);
v_a_5410_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5412_ = v___x_5364_;
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5364_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5415_; 
if (v_isShared_5413_ == 0)
{
v___x_5415_ = v___x_5412_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
}
else
{
lean_dec(v_a_5193_);
lean_dec(v_snd_5192_);
lean_dec(v_tail_5190_);
lean_del_object(v___x_5181_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_mantissa_5183_);
lean_del_object(v___x_5181_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_exponent_5184_);
lean_dec(v_mantissa_5183_);
lean_del_object(v___x_5181_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec_ref(v_fst_4514_);
if (lean_obj_tag(v_snd_4515_) == 2)
{
lean_object* v_n_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5546_; 
v_n_5419_ = lean_ctor_get(v_snd_4515_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v_snd_4515_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5421_ = v_snd_4515_;
v_isShared_5422_ = v_isSharedCheck_5546_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_n_5419_);
lean_dec(v_snd_4515_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5546_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v_mantissa_5423_; lean_object* v_exponent_5424_; lean_object* v_natZero_5425_; lean_object* v_intZero_5426_; uint8_t v_isNeg_5427_; 
v_mantissa_5423_ = lean_ctor_get(v_n_5419_, 0);
lean_inc(v_mantissa_5423_);
v_exponent_5424_ = lean_ctor_get(v_n_5419_, 1);
lean_inc(v_exponent_5424_);
lean_dec_ref(v_n_5419_);
v_natZero_5425_ = lean_unsigned_to_nat(0u);
v_intZero_5426_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5427_ = lean_int_dec_lt(v_mantissa_5423_, v_intZero_5426_);
if (v_isNeg_5427_ == 0)
{
uint8_t v___x_5428_; 
v___x_5428_ = lean_nat_dec_eq(v_exponent_5424_, v_natZero_5425_);
lean_dec(v_exponent_5424_);
if (v___x_5428_ == 0)
{
lean_dec(v_mantissa_5423_);
lean_del_object(v___x_5421_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_4516_) == 1)
{
lean_object* v_head_5429_; lean_object* v_tail_5430_; lean_object* v_fst_5431_; lean_object* v_snd_5432_; lean_object* v_a_5433_; lean_object* v___x_5434_; uint8_t v___x_5435_; 
v_head_5429_ = lean_ctor_get(v_tail_4516_, 0);
lean_inc(v_head_5429_);
v_tail_5430_ = lean_ctor_get(v_tail_4516_, 1);
lean_inc(v_tail_5430_);
lean_dec_ref_known(v_tail_4516_, 2);
v_fst_5431_ = lean_ctor_get(v_head_5429_, 0);
lean_inc(v_fst_5431_);
v_snd_5432_ = lean_ctor_get(v_head_5429_, 1);
lean_inc(v_snd_5432_);
lean_dec(v_head_5429_);
v_a_5433_ = lean_nat_abs(v_mantissa_5423_);
lean_dec(v_mantissa_5423_);
v___x_5434_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_5435_ = lean_string_dec_eq(v_fst_5431_, v___x_5434_);
if (v___x_5435_ == 0)
{
lean_object* v___x_5436_; uint8_t v___x_5437_; 
v___x_5436_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24));
v___x_5437_ = lean_string_dec_eq(v_fst_5431_, v___x_5436_);
lean_dec(v_fst_5431_);
if (v___x_5437_ == 0)
{
lean_dec(v_a_5433_);
lean_dec(v_snd_5432_);
lean_dec(v_tail_5430_);
lean_del_object(v___x_5421_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
else
{
if (lean_obj_tag(v_tail_5430_) == 0)
{
lean_object* v___x_5438_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5438_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_snd_5432_, v_a_4479_);
lean_dec(v_snd_5432_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5483_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5483_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5483_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v_snd_5443_; lean_object* v_fst_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5482_; 
v_snd_5443_ = lean_ctor_get(v_a_5439_, 1);
v_fst_5444_ = lean_ctor_get(v_a_5439_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v_a_5439_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5446_ = v_a_5439_;
v_isShared_5447_ = v_isSharedCheck_5482_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_snd_5443_);
lean_inc(v_fst_5444_);
lean_dec(v_a_5439_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5482_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v_stream_5448_; lean_object* v_nameMap_5449_; lean_object* v_levelMap_5450_; lean_object* v_exprMap_5451_; lean_object* v_recursorRuleMap_5452_; lean_object* v_constMap_5453_; lean_object* v_constOrder_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5481_; 
v_stream_5448_ = lean_ctor_get(v_snd_5443_, 0);
v_nameMap_5449_ = lean_ctor_get(v_snd_5443_, 1);
v_levelMap_5450_ = lean_ctor_get(v_snd_5443_, 2);
v_exprMap_5451_ = lean_ctor_get(v_snd_5443_, 3);
v_recursorRuleMap_5452_ = lean_ctor_get(v_snd_5443_, 4);
v_constMap_5453_ = lean_ctor_get(v_snd_5443_, 5);
v_constOrder_5454_ = lean_ctor_get(v_snd_5443_, 6);
v_isSharedCheck_5481_ = !lean_is_exclusive(v_snd_5443_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5456_ = v_snd_5443_;
v_isShared_5457_ = v_isSharedCheck_5481_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_constOrder_5454_);
lean_inc(v_constMap_5453_);
lean_inc(v_recursorRuleMap_5452_);
lean_inc(v_exprMap_5451_);
lean_inc(v_levelMap_5450_);
lean_inc(v_nameMap_5449_);
lean_inc(v_stream_5448_);
lean_dec(v_snd_5443_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5481_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
uint8_t v___x_5458_; 
v___x_5458_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_nameMap_5449_, v_a_5433_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5462_; 
lean_del_object(v___x_5421_);
v___x_5459_ = lean_box(0);
v___x_5460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5449_, v_a_5433_, v_fst_5444_);
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 1, v___x_5460_);
v___x_5462_ = v___x_5456_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_stream_5448_);
lean_ctor_set(v_reuseFailAlloc_5469_, 1, v___x_5460_);
lean_ctor_set(v_reuseFailAlloc_5469_, 2, v_levelMap_5450_);
lean_ctor_set(v_reuseFailAlloc_5469_, 3, v_exprMap_5451_);
lean_ctor_set(v_reuseFailAlloc_5469_, 4, v_recursorRuleMap_5452_);
lean_ctor_set(v_reuseFailAlloc_5469_, 5, v_constMap_5453_);
lean_ctor_set(v_reuseFailAlloc_5469_, 6, v_constOrder_5454_);
v___x_5462_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
lean_object* v___x_5464_; 
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 1, v___x_5462_);
lean_ctor_set(v___x_5446_, 0, v___x_5459_);
v___x_5464_ = v___x_5446_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5468_, 1, v___x_5462_);
v___x_5464_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
lean_object* v___x_5466_; 
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v___x_5464_);
v___x_5466_ = v___x_5441_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
else
{
lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5476_; 
lean_del_object(v___x_5456_);
lean_dec_ref(v_constOrder_5454_);
lean_dec_ref(v_constMap_5453_);
lean_dec_ref(v_recursorRuleMap_5452_);
lean_dec_ref(v_exprMap_5451_);
lean_dec_ref(v_levelMap_5450_);
lean_dec_ref(v_nameMap_5449_);
lean_dec_ref(v_stream_5448_);
lean_del_object(v___x_5446_);
lean_dec(v_fst_5444_);
v___x_5470_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_5471_ = l_Nat_reprFast(v_a_5433_);
v___x_5472_ = lean_string_append(v___x_5470_, v___x_5471_);
lean_dec_ref(v___x_5471_);
v___x_5473_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5474_ = lean_string_append(v___x_5472_, v___x_5473_);
if (v_isShared_5422_ == 0)
{
lean_ctor_set_tag(v___x_5421_, 18);
lean_ctor_set(v___x_5421_, 0, v___x_5474_);
v___x_5476_ = v___x_5421_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5478_; 
if (v_isShared_5442_ == 0)
{
lean_ctor_set_tag(v___x_5441_, 1);
lean_ctor_set(v___x_5441_, 0, v___x_5476_);
v___x_5478_ = v___x_5441_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
lean_dec(v_a_5433_);
lean_del_object(v___x_5421_);
v_a_5484_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5438_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5438_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
else
{
lean_dec(v_a_5433_);
lean_dec(v_snd_5432_);
lean_dec(v_tail_5430_);
lean_del_object(v___x_5421_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_fst_5431_);
if (lean_obj_tag(v_tail_5430_) == 0)
{
lean_object* v___x_5492_; 
lean_del_object(v___x_4499_);
lean_dec(v_kvPairs_4497_);
lean_del_object(v___x_4495_);
v___x_5492_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_snd_5432_, v_a_4479_);
lean_dec(v_snd_5432_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5537_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5495_ = v___x_5492_;
v_isShared_5496_ = v_isSharedCheck_5537_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5492_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5537_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_snd_5497_; lean_object* v_fst_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5536_; 
v_snd_5497_ = lean_ctor_get(v_a_5493_, 1);
v_fst_5498_ = lean_ctor_get(v_a_5493_, 0);
v_isSharedCheck_5536_ = !lean_is_exclusive(v_a_5493_);
if (v_isSharedCheck_5536_ == 0)
{
v___x_5500_ = v_a_5493_;
v_isShared_5501_ = v_isSharedCheck_5536_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_snd_5497_);
lean_inc(v_fst_5498_);
lean_dec(v_a_5493_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5536_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v_stream_5502_; lean_object* v_nameMap_5503_; lean_object* v_levelMap_5504_; lean_object* v_exprMap_5505_; lean_object* v_recursorRuleMap_5506_; lean_object* v_constMap_5507_; lean_object* v_constOrder_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5535_; 
v_stream_5502_ = lean_ctor_get(v_snd_5497_, 0);
v_nameMap_5503_ = lean_ctor_get(v_snd_5497_, 1);
v_levelMap_5504_ = lean_ctor_get(v_snd_5497_, 2);
v_exprMap_5505_ = lean_ctor_get(v_snd_5497_, 3);
v_recursorRuleMap_5506_ = lean_ctor_get(v_snd_5497_, 4);
v_constMap_5507_ = lean_ctor_get(v_snd_5497_, 5);
v_constOrder_5508_ = lean_ctor_get(v_snd_5497_, 6);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_snd_5497_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5510_ = v_snd_5497_;
v_isShared_5511_ = v_isSharedCheck_5535_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_constOrder_5508_);
lean_inc(v_constMap_5507_);
lean_inc(v_recursorRuleMap_5506_);
lean_inc(v_exprMap_5505_);
lean_inc(v_levelMap_5504_);
lean_inc(v_nameMap_5503_);
lean_inc(v_stream_5502_);
lean_dec(v_snd_5497_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5535_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
uint8_t v___x_5512_; 
v___x_5512_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_nameMap_5503_, v_a_5433_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5516_; 
lean_del_object(v___x_5421_);
v___x_5513_ = lean_box(0);
v___x_5514_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5503_, v_a_5433_, v_fst_5498_);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5514_);
v___x_5516_ = v___x_5510_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_stream_5502_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_levelMap_5504_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_exprMap_5505_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_recursorRuleMap_5506_);
lean_ctor_set(v_reuseFailAlloc_5523_, 5, v_constMap_5507_);
lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_constOrder_5508_);
v___x_5516_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5518_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 1, v___x_5516_);
lean_ctor_set(v___x_5500_, 0, v___x_5513_);
v___x_5518_ = v___x_5500_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5516_);
v___x_5518_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5520_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5518_);
v___x_5520_ = v___x_5495_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
else
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5530_; 
lean_del_object(v___x_5510_);
lean_dec_ref(v_constOrder_5508_);
lean_dec_ref(v_constMap_5507_);
lean_dec_ref(v_recursorRuleMap_5506_);
lean_dec_ref(v_exprMap_5505_);
lean_dec_ref(v_levelMap_5504_);
lean_dec_ref(v_nameMap_5503_);
lean_dec_ref(v_stream_5502_);
lean_del_object(v___x_5500_);
lean_dec(v_fst_5498_);
v___x_5524_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__0));
v___x_5525_ = l_Nat_reprFast(v_a_5433_);
v___x_5526_ = lean_string_append(v___x_5524_, v___x_5525_);
lean_dec_ref(v___x_5525_);
v___x_5527_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addName___closed__1));
v___x_5528_ = lean_string_append(v___x_5526_, v___x_5527_);
if (v_isShared_5422_ == 0)
{
lean_ctor_set_tag(v___x_5421_, 18);
lean_ctor_set(v___x_5421_, 0, v___x_5528_);
v___x_5530_ = v___x_5421_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5528_);
v___x_5530_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
lean_object* v___x_5532_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set_tag(v___x_5495_, 1);
lean_ctor_set(v___x_5495_, 0, v___x_5530_);
v___x_5532_ = v___x_5495_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5530_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
lean_dec(v_a_5433_);
lean_del_object(v___x_5421_);
v_a_5538_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5492_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5492_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
else
{
lean_dec(v_a_5433_);
lean_dec(v_snd_5432_);
lean_dec(v_tail_5430_);
lean_del_object(v___x_5421_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_mantissa_5423_);
lean_del_object(v___x_5421_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_exponent_5424_);
lean_dec(v_mantissa_5423_);
lean_del_object(v___x_5421_);
lean_dec(v_tail_4516_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
else
{
lean_dec(v_tail_4516_);
lean_dec(v_snd_4515_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
v___jp_5547_:
{
if (lean_obj_tag(v___y_5548_) == 1)
{
lean_object* v_head_5549_; lean_object* v_tail_5550_; lean_object* v_fst_5551_; lean_object* v_snd_5552_; 
v_head_5549_ = lean_ctor_get(v___y_5548_, 0);
lean_inc(v_head_5549_);
v_tail_5550_ = lean_ctor_get(v___y_5548_, 1);
lean_inc(v_tail_5550_);
lean_dec_ref_known(v___y_5548_, 2);
v_fst_5551_ = lean_ctor_get(v_head_5549_, 0);
lean_inc(v_fst_5551_);
v_snd_5552_ = lean_ctor_get(v_head_5549_, 1);
lean_inc(v_snd_5552_);
lean_dec(v_head_5549_);
v_fst_4514_ = v_fst_5551_;
v_snd_4515_ = v_snd_5552_;
v_tail_4516_ = v_tail_5550_;
goto v___jp_4513_;
}
else
{
lean_dec(v___y_5548_);
lean_dec_ref(v_a_4479_);
goto v___jp_4501_;
}
}
}
}
else
{
lean_object* v___x_5582_; lean_object* v___x_5584_; 
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4479_);
v___x_5582_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_5582_);
v___x_5584_ = v___x_4495_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5582_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem_0interp(lean_interpreter_value* stack)
{
lean_object* v_line_4478_ = stack[0].m_obj;
lean_object* v_a_4479_ = stack[1].m_obj;
lean_object* v_res_5587_;
v_res_5587_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_line_4478_, v_a_4479_);
stack->m_obj
 = v_res_5587_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___boxed(lean_object* v_line_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_){
_start:
{
lean_object* v_res_5591_; 
v_res_5591_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_line_5588_, v_a_5589_);
return v_res_5591_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object* v_00_u03b2_5592_, lean_object* v_m_5593_, lean_object* v_a_5594_){
_start:
{
uint8_t v___x_5595_; 
v___x_5595_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___redArg(v_m_5593_, v_a_5594_);
return v___x_5595_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_5593_ = stack[1].m_obj;
lean_object* v_a_5594_ = stack[2].m_obj;
uint8_t v_res_5596_;
v_res_5596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_box(0), v_m_5593_, v_a_5594_);
stack->m_num = v_res_5596_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object* v_00_u03b2_5597_, lean_object* v_m_5598_, lean_object* v_a_5599_){
_start:
{
uint8_t v_res_5600_; lean_object* v_r_5601_; 
v_res_5600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_00_u03b2_5597_, v_m_5598_, v_a_5599_);
lean_dec(v_a_5599_);
lean_dec_ref(v_m_5598_);
v_r_5601_ = lean_box(v_res_5600_);
return v_r_5601_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(lean_object* v_a_5602_){
_start:
{
lean_object* v_stream_5604_; lean_object* v_getLine_5605_; lean_object* v___x_5606_; 
v_stream_5604_ = lean_ctor_get(v_a_5602_, 0);
v_getLine_5605_ = lean_ctor_get(v_stream_5604_, 3);
lean_inc_ref(v_getLine_5605_);
v___x_5606_ = lean_apply_1(v_getLine_5605_, lean_box(0));
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5623_; 
v_a_5607_ = lean_ctor_get(v___x_5606_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5609_ = v___x_5606_;
v_isShared_5610_ = v_isSharedCheck_5623_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5606_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5623_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; uint8_t v___x_5613_; 
v___x_5611_ = lean_string_utf8_byte_size(v_a_5607_);
v___x_5612_ = lean_unsigned_to_nat(0u);
v___x_5613_ = lean_nat_dec_eq(v___x_5611_, v___x_5612_);
if (v___x_5613_ == 0)
{
lean_object* v___x_5614_; 
lean_del_object(v___x_5609_);
v___x_5614_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_a_5607_, v_a_5602_);
if (lean_obj_tag(v___x_5614_) == 0)
{
lean_object* v_a_5615_; lean_object* v_snd_5616_; 
v_a_5615_ = lean_ctor_get(v___x_5614_, 0);
lean_inc(v_a_5615_);
lean_dec_ref_known(v___x_5614_, 1);
v_snd_5616_ = lean_ctor_get(v_a_5615_, 1);
lean_inc(v_snd_5616_);
lean_dec(v_a_5615_);
v_a_5602_ = v_snd_5616_;
goto _start;
}
else
{
return v___x_5614_;
}
}
else
{
lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5621_; 
lean_dec(v_a_5607_);
v___x_5618_ = lean_box(0);
v___x_5619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
lean_ctor_set(v___x_5619_, 1, v_a_5602_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 0, v___x_5619_);
v___x_5621_ = v___x_5609_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref(v_a_5602_);
v_a_5624_ = lean_ctor_get(v___x_5606_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5606_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5606_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5602_ = stack[0].m_obj;
lean_object* v_res_5632_;
v_res_5632_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5602_);
stack->m_obj
 = v_res_5632_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go___boxed(lean_object* v_a_5633_, lean_object* v_a_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5633_);
return v_res_5635_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(lean_object* v_a_5636_){
_start:
{
lean_object* v___x_5638_; 
v___x_5638_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5636_);
return v___x_5638_;
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5636_ = stack[0].m_obj;
lean_object* v_res_5639_;
v_res_5639_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(v_a_5636_);
stack->m_obj
 = v_res_5639_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems___boxed(lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v_res_5642_; 
v_res_5642_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(v_a_5640_);
return v_res_5642_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(lean_object* v_a_5643_){
_start:
{
lean_object* v_stream_5645_; lean_object* v_getLine_5646_; lean_object* v___x_5647_; 
v_stream_5645_ = lean_ctor_get(v_a_5643_, 0);
v_getLine_5646_ = lean_ctor_get(v_stream_5645_, 3);
lean_inc_ref(v_getLine_5646_);
v___x_5647_ = lean_apply_1(v_getLine_5646_, lean_box(0));
if (lean_obj_tag(v___x_5647_) == 0)
{
lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5656_; 
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5656_ == 0)
{
lean_object* v_unused_5657_; 
v_unused_5657_ = lean_ctor_get(v___x_5647_, 0);
lean_dec(v_unused_5657_);
v___x_5649_ = v___x_5647_;
v_isShared_5650_ = v_isSharedCheck_5656_;
goto v_resetjp_5648_;
}
else
{
lean_dec(v___x_5647_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5656_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5654_; 
v___x_5651_ = lean_box(0);
v___x_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5651_);
lean_ctor_set(v___x_5652_, 1, v_a_5643_);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 0, v___x_5652_);
v___x_5654_ = v___x_5649_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec_ref(v_a_5643_);
v_a_5658_ = lean_ctor_get(v___x_5647_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5647_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5647_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5643_ = stack[0].m_obj;
lean_object* v_res_5666_;
v_res_5666_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5643_);
stack->m_obj
 = v_res_5666_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata___boxed(lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5667_);
return v_res_5669_;
}
}
lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(lean_object* v_a_5670_){
_start:
{
lean_object* v___x_5672_; 
v___x_5672_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5670_);
if (lean_obj_tag(v___x_5672_) == 0)
{
lean_object* v_a_5673_; lean_object* v_snd_5674_; lean_object* v___x_5675_; 
v_a_5673_ = lean_ctor_get(v___x_5672_, 0);
lean_inc(v_a_5673_);
lean_dec_ref_known(v___x_5672_, 1);
v_snd_5674_ = lean_ctor_get(v_a_5673_, 1);
lean_inc(v_snd_5674_);
lean_dec(v_a_5673_);
v___x_5675_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_snd_5674_);
return v___x_5675_;
}
else
{
return v___x_5672_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5670_ = stack[0].m_obj;
lean_object* v_res_5676_;
v_res_5676_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(v_a_5670_);
stack->m_obj
 = v_res_5676_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed(lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(v_a_5677_);
return v_res_5679_;
}
}
lean_object* l_LeanExport_parseStream(lean_object* v_stream_5680_){
_start:
{
lean_object* v___x_5682_; lean_object* v___x_5683_; 
v___x_5682_ = lean_alloc_closure((void*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed), 2, 0);
v___x_5683_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v___x_5682_, v_stream_5680_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5702_; 
v_a_5684_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5686_ = v___x_5683_;
v_isShared_5687_ = v_isSharedCheck_5702_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5683_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5702_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v_snd_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5700_; 
v_snd_5688_ = lean_ctor_get(v_a_5684_, 1);
v_isSharedCheck_5700_ = !lean_is_exclusive(v_a_5684_);
if (v_isSharedCheck_5700_ == 0)
{
lean_object* v_unused_5701_; 
v_unused_5701_ = lean_ctor_get(v_a_5684_, 0);
lean_dec(v_unused_5701_);
v___x_5690_ = v_a_5684_;
v_isShared_5691_ = v_isSharedCheck_5700_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_snd_5688_);
lean_dec(v_a_5684_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5700_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v_constMap_5692_; lean_object* v_constOrder_5693_; lean_object* v___x_5695_; 
v_constMap_5692_ = lean_ctor_get(v_snd_5688_, 5);
lean_inc_ref(v_constMap_5692_);
v_constOrder_5693_ = lean_ctor_get(v_snd_5688_, 6);
lean_inc_ref(v_constOrder_5693_);
lean_dec(v_snd_5688_);
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 1, v_constOrder_5693_);
lean_ctor_set(v___x_5690_, 0, v_constMap_5692_);
v___x_5695_ = v___x_5690_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_constMap_5692_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v_constOrder_5693_);
v___x_5695_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v___x_5695_);
v___x_5697_ = v___x_5686_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
}
else
{
lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5710_; 
v_a_5703_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5705_ = v___x_5683_;
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___x_5683_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5708_; 
if (v_isShared_5706_ == 0)
{
v___x_5708_ = v___x_5705_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_a_5703_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
}
}
LEAN_EXPORT void l_LeanExport_parseStream_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_5680_ = stack[0].m_obj;
lean_object* v_res_5711_;
v_res_5711_ = l_LeanExport_parseStream(v_stream_5680_);
stack->m_obj
 = v_res_5711_;
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream___boxed(lean_object* v_stream_5712_, lean_object* v_a_5713_){
_start:
{
lean_object* v_res_5714_; 
v_res_5714_ = l_LeanExport_parseStream(v_stream_5712_);
return v_res_5714_;
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

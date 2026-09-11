// Lean compiler output
// Module: LeanExport.Parse
// Imports: public import Std.Data.HashMap public import Lean.Declaration import Init.Data.Array.GetLit import Init.Data.String.Search import Init.System.IO import Std.Internal.Parsec.String import Lean.Data.Json.Parser
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
lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Level not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Expr not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "RecursorRule not found "};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Expected JSON object"};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__0_value)}};
static const lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1 = (const lean_object*)&l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1_value;
static const lean_closure_object l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Parser_anyCore, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object* v_nidx_257_, lean_object* v_n_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_stream_261_; lean_object* v_nameMap_262_; lean_object* v_levelMap_263_; lean_object* v_exprMap_264_; lean_object* v_recursorRuleMap_265_; lean_object* v_constMap_266_; lean_object* v_constOrder_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_280_; 
v_stream_261_ = lean_ctor_get(v_a_259_, 0);
v_nameMap_262_ = lean_ctor_get(v_a_259_, 1);
v_levelMap_263_ = lean_ctor_get(v_a_259_, 2);
v_exprMap_264_ = lean_ctor_get(v_a_259_, 3);
v_recursorRuleMap_265_ = lean_ctor_get(v_a_259_, 4);
v_constMap_266_ = lean_ctor_get(v_a_259_, 5);
v_constOrder_267_ = lean_ctor_get(v_a_259_, 6);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_259_);
if (v_isSharedCheck_280_ == 0)
{
v___x_269_ = v_a_259_;
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_constOrder_267_);
lean_inc(v_constMap_266_);
lean_inc(v_recursorRuleMap_265_);
lean_inc(v_exprMap_264_);
lean_inc(v_levelMap_263_);
lean_inc(v_nameMap_262_);
lean_inc(v_stream_261_);
lean_dec(v_a_259_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___f_271_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_272_ = lean_box(0);
v___f_273_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_273_, v___f_271_, v_nameMap_262_, v_nidx_257_, v_n_258_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_274_);
v___x_276_ = v___x_269_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_stream_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_levelMap_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_exprMap_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_recursorRuleMap_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_constMap_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_constOrder_267_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object* v_nidx_281_, lean_object* v_n_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addName(v_nidx_281_, v_n_282_, v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object* v_uidx_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_levelMap_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_levelMap_290_ = lean_ctor_get(v_a_288_, 2);
v___f_291_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_292_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_287_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_292_, v___f_291_, v_levelMap_290_, v_uidx_287_);
if (lean_obj_tag(v___x_293_) == 1)
{
lean_object* v_val_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_uidx_287_);
v_val_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_val_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_val_294_);
lean_ctor_set(v___x_298_, 1, v_a_288_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v___x_293_);
lean_dec_ref(v_a_288_);
v___x_303_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_304_ = l_Nat_reprFast(v_uidx_287_);
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
lean_dec_ref(v___x_304_);
v___x_306_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object* v_uidx_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(v_uidx_308_, v_a_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object* v_uidx_312_, lean_object* v_l_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_stream_316_; lean_object* v_nameMap_317_; lean_object* v_levelMap_318_; lean_object* v_exprMap_319_; lean_object* v_recursorRuleMap_320_; lean_object* v_constMap_321_; lean_object* v_constOrder_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_335_; 
v_stream_316_ = lean_ctor_get(v_a_314_, 0);
v_nameMap_317_ = lean_ctor_get(v_a_314_, 1);
v_levelMap_318_ = lean_ctor_get(v_a_314_, 2);
v_exprMap_319_ = lean_ctor_get(v_a_314_, 3);
v_recursorRuleMap_320_ = lean_ctor_get(v_a_314_, 4);
v_constMap_321_ = lean_ctor_get(v_a_314_, 5);
v_constOrder_322_ = lean_ctor_get(v_a_314_, 6);
v_isSharedCheck_335_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_335_ == 0)
{
v___x_324_ = v_a_314_;
v_isShared_325_ = v_isSharedCheck_335_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_constOrder_322_);
lean_inc(v_constMap_321_);
lean_inc(v_recursorRuleMap_320_);
lean_inc(v_exprMap_319_);
lean_inc(v_levelMap_318_);
lean_inc(v_nameMap_317_);
lean_inc(v_stream_316_);
lean_dec(v_a_314_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_335_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___f_326_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_327_ = lean_box(0);
v___f_328_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_328_, v___f_326_, v_levelMap_318_, v_uidx_312_, v_l_313_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 2, v___x_329_);
v___x_331_ = v___x_324_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_stream_316_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_nameMap_317_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_exprMap_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_recursorRuleMap_320_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v_constMap_321_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_constOrder_322_);
v___x_331_ = v_reuseFailAlloc_334_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_327_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object* v_uidx_336_, lean_object* v_l_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(v_uidx_336_, v_l_337_, v_a_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object* v_eidx_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_exprMap_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___x_348_; 
v_exprMap_345_ = lean_ctor_get(v_a_343_, 3);
v___f_346_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_347_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_342_);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_347_, v___f_346_, v_exprMap_345_, v_eidx_342_);
if (lean_obj_tag(v___x_348_) == 1)
{
lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_eidx_342_);
v_val_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_val_349_);
lean_ctor_set(v___x_353_, 1, v_a_343_);
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 0);
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
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
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v___x_348_);
lean_dec_ref(v_a_343_);
v___x_358_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_359_ = l_Nat_reprFast(v_eidx_342_);
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object* v_eidx_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(v_eidx_363_, v_a_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object* v_eidx_367_, lean_object* v_e_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_stream_371_; lean_object* v_nameMap_372_; lean_object* v_levelMap_373_; lean_object* v_exprMap_374_; lean_object* v_recursorRuleMap_375_; lean_object* v_constMap_376_; lean_object* v_constOrder_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_390_; 
v_stream_371_ = lean_ctor_get(v_a_369_, 0);
v_nameMap_372_ = lean_ctor_get(v_a_369_, 1);
v_levelMap_373_ = lean_ctor_get(v_a_369_, 2);
v_exprMap_374_ = lean_ctor_get(v_a_369_, 3);
v_recursorRuleMap_375_ = lean_ctor_get(v_a_369_, 4);
v_constMap_376_ = lean_ctor_get(v_a_369_, 5);
v_constOrder_377_ = lean_ctor_get(v_a_369_, 6);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_369_);
if (v_isSharedCheck_390_ == 0)
{
v___x_379_ = v_a_369_;
v_isShared_380_ = v_isSharedCheck_390_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_constOrder_377_);
lean_inc(v_constMap_376_);
lean_inc(v_recursorRuleMap_375_);
lean_inc(v_exprMap_374_);
lean_inc(v_levelMap_373_);
lean_inc(v_nameMap_372_);
lean_inc(v_stream_371_);
lean_dec(v_a_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_390_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___f_381_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_382_ = lean_box(0);
v___f_383_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_383_, v___f_381_, v_exprMap_374_, v_eidx_367_, v_e_368_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 3, v___x_384_);
v___x_386_ = v___x_379_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_stream_371_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_nameMap_372_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_levelMap_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_recursorRuleMap_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v_constMap_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 6, v_constOrder_377_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_382_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object* v_eidx_391_, lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(v_eidx_391_, v_e_392_, v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object* v_ridx_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_recursorRuleMap_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
v_recursorRuleMap_400_ = lean_ctor_get(v_a_398_, 4);
v___f_401_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_402_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_397_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_402_, v___f_401_, v_recursorRuleMap_400_, v_ridx_397_);
if (lean_obj_tag(v___x_403_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_ridx_397_);
v_val_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_val_404_);
lean_ctor_set(v___x_408_, 1, v_a_398_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_398_);
v___x_413_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0));
v___x_414_ = l_Nat_reprFast(v_ridx_397_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object* v_ridx_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(v_ridx_418_, v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(lean_object* v_ridx_422_, lean_object* v_r_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_stream_426_; lean_object* v_nameMap_427_; lean_object* v_levelMap_428_; lean_object* v_exprMap_429_; lean_object* v_recursorRuleMap_430_; lean_object* v_constMap_431_; lean_object* v_constOrder_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_445_; 
v_stream_426_ = lean_ctor_get(v_a_424_, 0);
v_nameMap_427_ = lean_ctor_get(v_a_424_, 1);
v_levelMap_428_ = lean_ctor_get(v_a_424_, 2);
v_exprMap_429_ = lean_ctor_get(v_a_424_, 3);
v_recursorRuleMap_430_ = lean_ctor_get(v_a_424_, 4);
v_constMap_431_ = lean_ctor_get(v_a_424_, 5);
v_constOrder_432_ = lean_ctor_get(v_a_424_, 6);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_445_ == 0)
{
v___x_434_ = v_a_424_;
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_constOrder_432_);
lean_inc(v_constMap_431_);
lean_inc(v_recursorRuleMap_430_);
lean_inc(v_exprMap_429_);
lean_inc(v_levelMap_428_);
lean_inc(v_nameMap_427_);
lean_inc(v_stream_426_);
lean_dec(v_a_424_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___f_436_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_437_ = lean_box(0);
v___f_438_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_438_, v___f_436_, v_recursorRuleMap_430_, v_ridx_422_, v_r_423_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v___x_439_);
v___x_441_ = v___x_434_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_stream_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_nameMap_427_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_levelMap_428_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_exprMap_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_constMap_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_constOrder_432_);
v___x_441_ = v_reuseFailAlloc_444_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_437_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___boxed(lean_object* v_ridx_446_, lean_object* v_r_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(v_ridx_446_, v_r_447_, v_a_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(lean_object* v_name_454_, lean_object* v_d_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_stream_458_; lean_object* v_nameMap_459_; lean_object* v_levelMap_460_; lean_object* v_exprMap_461_; lean_object* v_recursorRuleMap_462_; lean_object* v_constMap_463_; lean_object* v_constOrder_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_484_; 
v_stream_458_ = lean_ctor_get(v_a_456_, 0);
v_nameMap_459_ = lean_ctor_get(v_a_456_, 1);
v_levelMap_460_ = lean_ctor_get(v_a_456_, 2);
v_exprMap_461_ = lean_ctor_get(v_a_456_, 3);
v_recursorRuleMap_462_ = lean_ctor_get(v_a_456_, 4);
v_constMap_463_ = lean_ctor_get(v_a_456_, 5);
v_constOrder_464_ = lean_ctor_get(v_a_456_, 6);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_484_ == 0)
{
v___x_466_ = v_a_456_;
v_isShared_467_ = v_isSharedCheck_484_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_constOrder_464_);
lean_inc(v_constMap_463_);
lean_inc(v_recursorRuleMap_462_);
lean_inc(v_exprMap_461_);
lean_inc(v_levelMap_460_);
lean_inc(v_nameMap_459_);
lean_inc(v_stream_458_);
lean_dec(v_a_456_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_484_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0));
v___x_469_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1));
lean_inc(v_name_454_);
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_468_, v___x_469_, v_constMap_463_, v_name_454_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_471_ = lean_box(0);
lean_inc(v_name_454_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_468_, v___x_469_, v_constMap_463_, v_name_454_, v_d_455_);
v___x_473_ = lean_array_push(v_constOrder_464_, v_name_454_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 6, v___x_473_);
lean_ctor_set(v___x_466_, 5, v___x_472_);
v___x_475_ = v___x_466_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_stream_458_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_nameMap_459_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_levelMap_460_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_exprMap_461_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_recursorRuleMap_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v___x_473_);
v___x_475_ = v_reuseFailAlloc_478_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_471_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_del_object(v___x_466_);
lean_dec_ref(v_constOrder_464_);
lean_dec_ref(v_constMap_463_);
lean_dec_ref(v_recursorRuleMap_462_);
lean_dec_ref(v_exprMap_461_);
lean_dec_ref(v_levelMap_460_);
lean_dec_ref(v_nameMap_459_);
lean_dec_ref(v_stream_458_);
lean_dec_ref(v_d_455_);
v___x_479_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_454_, v___x_470_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___boxed(lean_object* v_name_485_, lean_object* v_d_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(v_name_485_, v_d_486_, v_a_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(lean_object* v_line_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
v___x_501_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_500_, v_line_494_);
if (lean_obj_tag(v___x_501_) == 1)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
if (lean_obj_tag(v_a_502_) == 5)
{
lean_object* v_kvPairs_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_kvPairs_503_ = lean_ctor_get(v_a_502_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_502_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_a_502_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_kvPairs_503_);
lean_dec(v_a_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_kvPairs_503_);
lean_ctor_set(v___x_507_, 1, v_a_495_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_dec(v_a_502_);
lean_dec_ref(v_a_495_);
goto v___jp_497_;
}
}
else
{
lean_dec_ref(v___x_501_);
lean_dec_ref(v_a_495_);
goto v___jp_497_;
}
v___jp_497_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1));
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___boxed(lean_object* v_line_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(v_line_512_, v_a_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_key_519_; lean_object* v_value_520_; lean_object* v_tail_521_; uint8_t v___x_522_; 
v_key_519_ = lean_ctor_get(v_x_517_, 0);
v_value_520_ = lean_ctor_get(v_x_517_, 1);
v_tail_521_ = lean_ctor_get(v_x_517_, 2);
v___x_522_ = lean_nat_dec_eq(v_key_519_, v_a_516_);
if (v___x_522_ == 0)
{
v_x_517_ = v_tail_521_;
goto _start;
}
else
{
lean_object* v___x_524_; 
lean_inc(v_value_520_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_value_520_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg___boxed(lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_buckets_530_; lean_object* v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v_fold_535_; uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_buckets_530_ = lean_ctor_get(v_m_528_, 1);
v___x_531_ = lean_array_get_size(v_buckets_530_);
v___x_532_ = lean_uint64_of_nat(v_a_529_);
v___x_533_ = 32ULL;
v___x_534_ = lean_uint64_shift_right(v___x_532_, v___x_533_);
v_fold_535_ = lean_uint64_xor(v___x_532_, v___x_534_);
v___x_536_ = 16ULL;
v___x_537_ = lean_uint64_shift_right(v_fold_535_, v___x_536_);
v___x_538_ = lean_uint64_xor(v_fold_535_, v___x_537_);
v___x_539_ = lean_uint64_to_usize(v___x_538_);
v___x_540_ = lean_usize_of_nat(v___x_531_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_sub(v___x_540_, v___x_541_);
v___x_543_ = lean_usize_land(v___x_539_, v___x_542_);
v___x_544_ = lean_array_uget_borrowed(v_buckets_530_, v___x_543_);
v___x_545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_529_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg___boxed(lean_object* v_m_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_m_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(lean_object* v_t_549_, lean_object* v_k_550_){
_start:
{
if (lean_obj_tag(v_t_549_) == 0)
{
lean_object* v_k_551_; lean_object* v_v_552_; lean_object* v_l_553_; lean_object* v_r_554_; uint8_t v___x_555_; 
v_k_551_ = lean_ctor_get(v_t_549_, 1);
v_v_552_ = lean_ctor_get(v_t_549_, 2);
v_l_553_ = lean_ctor_get(v_t_549_, 3);
v_r_554_ = lean_ctor_get(v_t_549_, 4);
v___x_555_ = lean_string_compare(v_k_550_, v_k_551_);
switch(v___x_555_)
{
case 0:
{
v_t_549_ = v_l_553_;
goto _start;
}
case 1:
{
lean_object* v___x_557_; 
lean_inc(v_v_552_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_v_552_);
return v___x_557_;
}
default: 
{
v_t_549_ = v_r_554_;
goto _start;
}
}
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg___boxed(lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_560_, v_k_561_);
lean_dec_ref(v_k_561_);
lean_dec(v_t_560_);
return v_res_562_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3(void){
_start:
{
lean_object* v_natZero_567_; lean_object* v_intZero_568_; 
v_natZero_567_ = lean_unsigned_to_nat(0u);
v_intZero_568_ = lean_nat_to_int(v_natZero_567_);
return v_intZero_568_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(lean_object* v_json_570_, lean_object* v_a_571_){
_start:
{
if (lean_obj_tag(v_json_570_) == 5)
{
lean_object* v_kvPairs_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_kvPairs_579_ = lean_ctor_get(v_json_570_, 0);
v___x_580_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_581_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_579_, v___x_580_);
if (lean_obj_tag(v___x_581_) == 1)
{
lean_object* v_val_582_; 
v_val_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_val_582_);
lean_dec_ref_known(v___x_581_, 1);
if (lean_obj_tag(v_val_582_) == 2)
{
lean_object* v_n_583_; lean_object* v_mantissa_584_; lean_object* v_exponent_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_629_; 
v_n_583_ = lean_ctor_get(v_val_582_, 0);
lean_inc_ref(v_n_583_);
lean_dec_ref_known(v_val_582_, 1);
v_mantissa_584_ = lean_ctor_get(v_n_583_, 0);
v_exponent_585_ = lean_ctor_get(v_n_583_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_n_583_);
if (v_isSharedCheck_629_ == 0)
{
v___x_587_ = v_n_583_;
v_isShared_588_ = v_isSharedCheck_629_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_exponent_585_);
lean_inc(v_mantissa_584_);
lean_dec(v_n_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_629_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_natZero_589_; lean_object* v_intZero_590_; uint8_t v_isNeg_591_; 
v_natZero_589_ = lean_unsigned_to_nat(0u);
v_intZero_590_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_591_ = lean_int_dec_lt(v_mantissa_584_, v_intZero_590_);
if (v_isNeg_591_ == 0)
{
uint8_t v___x_592_; 
v___x_592_ = lean_nat_dec_eq(v_exponent_585_, v_natZero_589_);
lean_dec(v_exponent_585_);
if (v___x_592_ == 0)
{
lean_del_object(v___x_587_);
lean_dec(v_mantissa_584_);
lean_dec_ref(v_a_571_);
goto v___jp_573_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_579_, v___x_593_);
if (lean_obj_tag(v___x_594_) == 1)
{
lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_628_; 
v_val_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_628_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_628_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_628_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_val_595_) == 3)
{
lean_object* v_s_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_627_; 
v_s_599_ = lean_ctor_get(v_val_595_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_val_595_);
if (v_isSharedCheck_627_ == 0)
{
v___x_601_ = v_val_595_;
v_isShared_602_ = v_isSharedCheck_627_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_s_599_);
lean_dec(v_val_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_627_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_nameMap_603_; lean_object* v_a_604_; lean_object* v___x_605_; 
v_nameMap_603_ = lean_ctor_get(v_a_571_, 1);
v_a_604_ = lean_nat_abs(v_mantissa_584_);
lean_dec(v_mantissa_584_);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_603_, v_a_604_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_604_);
lean_del_object(v___x_601_);
lean_del_object(v___x_597_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_617_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Name_str___override(v_val_606_, v_s_599_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_a_571_);
lean_ctor_set(v___x_587_, 0, v___x_610_);
v___x_612_ = v___x_587_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_a_571_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 0);
lean_ctor_set(v___x_608_, 0, v___x_612_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec(v___x_605_);
lean_dec_ref(v_s_599_);
lean_del_object(v___x_587_);
lean_dec_ref(v_a_571_);
v___x_618_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_619_ = l_Nat_reprFast(v_a_604_);
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
lean_dec_ref(v___x_619_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 18);
lean_ctor_set(v___x_601_, 0, v___x_620_);
v___x_622_ = v___x_601_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_622_);
v___x_624_ = v___x_597_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
lean_del_object(v___x_597_);
lean_dec(v_val_595_);
lean_del_object(v___x_587_);
lean_dec(v_mantissa_584_);
lean_dec_ref(v_a_571_);
goto v___jp_576_;
}
}
}
else
{
lean_dec(v___x_594_);
lean_del_object(v___x_587_);
lean_dec(v_mantissa_584_);
lean_dec_ref(v_a_571_);
goto v___jp_576_;
}
}
}
else
{
lean_del_object(v___x_587_);
lean_dec(v_exponent_585_);
lean_dec(v_mantissa_584_);
lean_dec_ref(v_a_571_);
goto v___jp_573_;
}
}
}
else
{
lean_dec(v_val_582_);
lean_dec_ref(v_a_571_);
goto v___jp_573_;
}
}
else
{
lean_dec(v___x_581_);
lean_dec_ref(v_a_571_);
goto v___jp_573_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_a_571_);
v___x_630_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
v___jp_573_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___boxed(lean_object* v_json_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_json_632_, v_a_633_);
lean_dec(v_json_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(lean_object* v_00_u03b4_636_, lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_637_, v_k_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___boxed(lean_object* v_00_u03b4_640_, lean_object* v_t_641_, lean_object* v_k_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(v_00_u03b4_640_, v_t_641_, v_k_642_);
lean_dec_ref(v_k_642_);
lean_dec(v_t_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(lean_object* v_00_u03b2_644_, lean_object* v_m_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_645_, v_a_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___boxed(lean_object* v_00_u03b2_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(v_00_u03b2_648_, v_m_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_m_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(lean_object* v_00_u03b2_652_, lean_object* v_a_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___boxed(lean_object* v_00_u03b2_656_, lean_object* v_a_657_, lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(v_00_u03b2_656_, v_a_657_, v_x_658_);
lean_dec(v_x_658_);
lean_dec(v_a_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(lean_object* v_json_664_, lean_object* v_a_665_){
_start:
{
if (lean_obj_tag(v_json_664_) == 5)
{
lean_object* v_kvPairs_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_kvPairs_673_ = lean_ctor_get(v_json_664_, 0);
v___x_674_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_675_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_673_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 1)
{
lean_object* v_val_676_; 
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
if (lean_obj_tag(v_val_676_) == 2)
{
lean_object* v_n_677_; lean_object* v_mantissa_678_; lean_object* v_exponent_679_; lean_object* v_natZero_680_; lean_object* v_intZero_681_; uint8_t v_isNeg_682_; 
v_n_677_ = lean_ctor_get(v_val_676_, 0);
lean_inc_ref(v_n_677_);
lean_dec_ref_known(v_val_676_, 1);
v_mantissa_678_ = lean_ctor_get(v_n_677_, 0);
lean_inc(v_mantissa_678_);
v_exponent_679_ = lean_ctor_get(v_n_677_, 1);
lean_inc(v_exponent_679_);
lean_dec_ref(v_n_677_);
v_natZero_680_ = lean_unsigned_to_nat(0u);
v_intZero_681_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_682_ = lean_int_dec_lt(v_mantissa_678_, v_intZero_681_);
if (v_isNeg_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = lean_nat_dec_eq(v_exponent_679_, v_natZero_680_);
lean_dec(v_exponent_679_);
if (v___x_683_ == 0)
{
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_667_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2));
v___x_685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_673_, v___x_684_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_728_; 
v_val_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_728_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_728_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_728_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
if (lean_obj_tag(v_val_686_) == 2)
{
lean_object* v_n_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_727_; 
v_n_690_ = lean_ctor_get(v_val_686_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_val_686_);
if (v_isSharedCheck_727_ == 0)
{
v___x_692_ = v_val_686_;
v_isShared_693_ = v_isSharedCheck_727_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_n_690_);
lean_dec(v_val_686_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_727_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_mantissa_694_; lean_object* v_exponent_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_726_; 
v_mantissa_694_ = lean_ctor_get(v_n_690_, 0);
v_exponent_695_ = lean_ctor_get(v_n_690_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_n_690_);
if (v_isSharedCheck_726_ == 0)
{
v___x_697_ = v_n_690_;
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_exponent_695_);
lean_inc(v_mantissa_694_);
lean_dec(v_n_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
uint8_t v_isNeg_699_; 
v_isNeg_699_ = lean_int_dec_lt(v_mantissa_694_, v_intZero_681_);
if (v_isNeg_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_eq(v_exponent_695_, v_natZero_680_);
lean_dec(v_exponent_695_);
if (v___x_700_ == 0)
{
lean_del_object(v___x_697_);
lean_dec(v_mantissa_694_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_670_;
}
else
{
lean_object* v_nameMap_701_; lean_object* v_a_702_; lean_object* v___x_703_; 
v_nameMap_701_ = lean_ctor_get(v_a_665_, 1);
v_a_702_ = lean_nat_abs(v_mantissa_678_);
lean_dec(v_mantissa_678_);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_701_, v_a_702_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_a_702_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
v_val_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_716_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_716_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_val_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_716_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v_a_708_ = lean_nat_abs(v_mantissa_694_);
lean_dec(v_mantissa_694_);
v___x_709_ = l_Lean_Name_num___override(v_val_704_, v_a_708_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_a_665_);
lean_ctor_set(v___x_697_, 0, v___x_709_);
v___x_711_ = v___x_697_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_665_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 0, v___x_711_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v___x_703_);
lean_del_object(v___x_697_);
lean_dec(v_mantissa_694_);
lean_dec_ref(v_a_665_);
v___x_717_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_718_ = l_Nat_reprFast(v_a_702_);
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
lean_dec_ref(v___x_718_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 18);
lean_ctor_set(v___x_692_, 0, v___x_719_);
v___x_721_ = v___x_692_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_721_);
v___x_723_ = v___x_688_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_del_object(v___x_697_);
lean_dec(v_exponent_695_);
lean_dec(v_mantissa_694_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_670_;
}
}
}
}
else
{
lean_del_object(v___x_688_);
lean_dec(v_val_686_);
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_670_;
}
}
}
else
{
lean_dec(v___x_685_);
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_670_;
}
}
}
else
{
lean_dec(v_exponent_679_);
lean_dec(v_mantissa_678_);
lean_dec_ref(v_a_665_);
goto v___jp_667_;
}
}
else
{
lean_dec(v_val_676_);
lean_dec_ref(v_a_665_);
goto v___jp_667_;
}
}
else
{
lean_dec(v___x_675_);
lean_dec_ref(v_a_665_);
goto v___jp_667_;
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_a_665_);
v___x_729_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
v___jp_667_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
v___jp_670_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___boxed(lean_object* v_json_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_json_731_, v_a_732_);
lean_dec(v_json_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(lean_object* v_json_738_, lean_object* v_a_739_){
_start:
{
if (lean_obj_tag(v_json_738_) == 2)
{
lean_object* v_n_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_780_; 
v_n_744_ = lean_ctor_get(v_json_738_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_json_738_);
if (v_isSharedCheck_780_ == 0)
{
v___x_746_ = v_json_738_;
v_isShared_747_ = v_isSharedCheck_780_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_n_744_);
lean_dec(v_json_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_780_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_mantissa_748_; lean_object* v_exponent_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_779_; 
v_mantissa_748_ = lean_ctor_get(v_n_744_, 0);
v_exponent_749_ = lean_ctor_get(v_n_744_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_n_744_);
if (v_isSharedCheck_779_ == 0)
{
v___x_751_ = v_n_744_;
v_isShared_752_ = v_isSharedCheck_779_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_exponent_749_);
lean_inc(v_mantissa_748_);
lean_dec(v_n_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_779_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_natZero_753_; lean_object* v_intZero_754_; uint8_t v_isNeg_755_; 
v_natZero_753_ = lean_unsigned_to_nat(0u);
v_intZero_754_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_755_ = lean_int_dec_lt(v_mantissa_748_, v_intZero_754_);
if (v_isNeg_755_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = lean_nat_dec_eq(v_exponent_749_, v_natZero_753_);
lean_dec(v_exponent_749_);
if (v___x_756_ == 0)
{
lean_del_object(v___x_751_);
lean_dec(v_mantissa_748_);
lean_del_object(v___x_746_);
lean_dec_ref(v_a_739_);
goto v___jp_741_;
}
else
{
lean_object* v_levelMap_757_; lean_object* v_a_758_; lean_object* v___x_759_; 
v_levelMap_757_ = lean_ctor_get(v_a_739_, 2);
v_a_758_ = lean_nat_abs(v_mantissa_748_);
lean_dec(v_mantissa_748_);
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_757_, v_a_758_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_a_758_);
lean_del_object(v___x_746_);
v_val_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_771_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_771_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = l_Lean_Level_succ___override(v_val_760_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_a_739_);
lean_ctor_set(v___x_751_, 0, v___x_764_);
v___x_766_ = v___x_751_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_739_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 0);
lean_ctor_set(v___x_762_, 0, v___x_766_);
v___x_768_ = v___x_762_;
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
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec(v___x_759_);
lean_del_object(v___x_751_);
lean_dec_ref(v_a_739_);
v___x_772_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_773_ = l_Nat_reprFast(v_a_758_);
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
lean_dec_ref(v___x_773_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 18);
lean_ctor_set(v___x_746_, 0, v___x_774_);
v___x_776_ = v___x_746_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
}
}
else
{
lean_del_object(v___x_751_);
lean_dec(v_exponent_749_);
lean_dec(v_mantissa_748_);
lean_del_object(v___x_746_);
lean_dec_ref(v_a_739_);
goto v___jp_741_;
}
}
}
}
else
{
lean_dec_ref(v_a_739_);
lean_dec(v_json_738_);
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1));
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___boxed(lean_object* v_json_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_json_781_, v_a_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(lean_object* v_json_788_, lean_object* v_a_789_){
_start:
{
if (lean_obj_tag(v_json_788_) == 4)
{
lean_object* v_elems_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_elems_794_ = lean_ctor_get(v_json_788_, 0);
v___x_795_ = lean_array_get_size(v_elems_794_);
v___x_796_ = lean_unsigned_to_nat(2u);
v___x_797_ = lean_nat_dec_eq(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_fget(v_elems_794_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 2)
{
lean_object* v_n_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_864_; 
v_n_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_864_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_864_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_n_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_864_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_mantissa_804_; lean_object* v_exponent_805_; lean_object* v_intZero_806_; uint8_t v_isNeg_807_; 
v_mantissa_804_ = lean_ctor_get(v_n_800_, 0);
lean_inc(v_mantissa_804_);
v_exponent_805_ = lean_ctor_get(v_n_800_, 1);
lean_inc(v_exponent_805_);
lean_dec_ref(v_n_800_);
v_intZero_806_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_807_ = lean_int_dec_lt(v_mantissa_804_, v_intZero_806_);
if (v_isNeg_807_ == 0)
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_eq(v_exponent_805_, v___x_798_);
lean_dec(v_exponent_805_);
if (v___x_808_ == 0)
{
lean_dec(v_mantissa_804_);
lean_del_object(v___x_802_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_array_fget(v_elems_794_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 2)
{
lean_object* v_n_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_863_; 
v_n_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_863_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_863_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_n_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_863_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_mantissa_815_; lean_object* v_exponent_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_862_; 
v_mantissa_815_ = lean_ctor_get(v_n_811_, 0);
v_exponent_816_ = lean_ctor_get(v_n_811_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_n_811_);
if (v_isSharedCheck_862_ == 0)
{
v___x_818_ = v_n_811_;
v_isShared_819_ = v_isSharedCheck_862_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_exponent_816_);
lean_inc(v_mantissa_815_);
lean_dec(v_n_811_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_862_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v_isNeg_820_; 
v_isNeg_820_ = lean_int_dec_lt(v_mantissa_815_, v_intZero_806_);
if (v_isNeg_820_ == 0)
{
uint8_t v___x_821_; 
v___x_821_ = lean_nat_dec_eq(v_exponent_816_, v___x_798_);
lean_dec(v_exponent_816_);
if (v___x_821_ == 0)
{
lean_del_object(v___x_818_);
lean_dec(v_mantissa_815_);
lean_del_object(v___x_813_);
lean_dec(v_mantissa_804_);
lean_del_object(v___x_802_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
else
{
lean_object* v_levelMap_822_; lean_object* v_a_823_; lean_object* v___x_824_; 
v_levelMap_822_ = lean_ctor_get(v_a_789_, 2);
v_a_823_ = lean_nat_abs(v_mantissa_804_);
lean_dec(v_mantissa_804_);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_822_, v_a_823_);
if (lean_obj_tag(v___x_824_) == 1)
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_a_823_);
lean_del_object(v___x_802_);
v_val_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_852_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_852_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_852_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_nat_abs(v_mantissa_815_);
lean_dec(v_mantissa_815_);
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_822_, v_a_829_);
if (lean_obj_tag(v___x_830_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_829_);
lean_del_object(v___x_827_);
lean_del_object(v___x_813_);
v_val_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_842_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = l_Lean_Level_max___override(v_val_825_, v_val_831_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_a_789_);
lean_ctor_set(v___x_818_, 0, v___x_835_);
v___x_837_ = v___x_818_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_789_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
lean_ctor_set(v___x_833_, 0, v___x_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v___x_830_);
lean_dec(v_val_825_);
lean_del_object(v___x_818_);
lean_dec_ref(v_a_789_);
v___x_843_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_844_ = l_Nat_reprFast(v_a_829_);
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
lean_dec_ref(v___x_844_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 18);
lean_ctor_set(v___x_827_, 0, v___x_845_);
v___x_847_ = v___x_827_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 1);
lean_ctor_set(v___x_813_, 0, v___x_847_);
v___x_849_ = v___x_813_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v___x_824_);
lean_del_object(v___x_818_);
lean_dec(v_mantissa_815_);
lean_dec_ref(v_a_789_);
v___x_853_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_854_ = l_Nat_reprFast(v_a_823_);
v___x_855_ = lean_string_append(v___x_853_, v___x_854_);
lean_dec_ref(v___x_854_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 18);
lean_ctor_set(v___x_813_, 0, v___x_855_);
v___x_857_ = v___x_813_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 1);
lean_ctor_set(v___x_802_, 0, v___x_857_);
v___x_859_ = v___x_802_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_818_);
lean_dec(v_exponent_816_);
lean_dec(v_mantissa_815_);
lean_del_object(v___x_813_);
lean_dec(v_mantissa_804_);
lean_del_object(v___x_802_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
}
}
}
else
{
lean_dec(v___x_810_);
lean_dec(v_mantissa_804_);
lean_del_object(v___x_802_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
}
}
else
{
lean_dec(v_exponent_805_);
lean_dec(v_mantissa_804_);
lean_del_object(v___x_802_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
}
}
else
{
lean_dec(v___x_799_);
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
}
}
else
{
lean_dec_ref(v_a_789_);
goto v___jp_791_;
}
v___jp_791_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1));
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___boxed(lean_object* v_json_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_json_865_, v_a_866_);
lean_dec(v_json_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(lean_object* v_json_872_, lean_object* v_a_873_){
_start:
{
if (lean_obj_tag(v_json_872_) == 4)
{
lean_object* v_elems_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_elems_878_ = lean_ctor_get(v_json_872_, 0);
v___x_879_ = lean_array_get_size(v_elems_878_);
v___x_880_ = lean_unsigned_to_nat(2u);
v___x_881_ = lean_nat_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_array_fget(v_elems_878_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 2)
{
lean_object* v_n_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_948_; 
v_n_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_948_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_948_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_n_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_948_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_mantissa_888_; lean_object* v_exponent_889_; lean_object* v_intZero_890_; uint8_t v_isNeg_891_; 
v_mantissa_888_ = lean_ctor_get(v_n_884_, 0);
lean_inc(v_mantissa_888_);
v_exponent_889_ = lean_ctor_get(v_n_884_, 1);
lean_inc(v_exponent_889_);
lean_dec_ref(v_n_884_);
v_intZero_890_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_891_ = lean_int_dec_lt(v_mantissa_888_, v_intZero_890_);
if (v_isNeg_891_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = lean_nat_dec_eq(v_exponent_889_, v___x_882_);
lean_dec(v_exponent_889_);
if (v___x_892_ == 0)
{
lean_dec(v_mantissa_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_array_fget(v_elems_878_, v___x_893_);
if (lean_obj_tag(v___x_894_) == 2)
{
lean_object* v_n_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_947_; 
v_n_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_947_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_947_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_n_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_947_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_mantissa_899_; lean_object* v_exponent_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_946_; 
v_mantissa_899_ = lean_ctor_get(v_n_895_, 0);
v_exponent_900_ = lean_ctor_get(v_n_895_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v_n_895_);
if (v_isSharedCheck_946_ == 0)
{
v___x_902_ = v_n_895_;
v_isShared_903_ = v_isSharedCheck_946_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_exponent_900_);
lean_inc(v_mantissa_899_);
lean_dec(v_n_895_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_946_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v_isNeg_904_; 
v_isNeg_904_ = lean_int_dec_lt(v_mantissa_899_, v_intZero_890_);
if (v_isNeg_904_ == 0)
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_eq(v_exponent_900_, v___x_882_);
lean_dec(v_exponent_900_);
if (v___x_905_ == 0)
{
lean_del_object(v___x_902_);
lean_dec(v_mantissa_899_);
lean_del_object(v___x_897_);
lean_dec(v_mantissa_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
else
{
lean_object* v_levelMap_906_; lean_object* v_a_907_; lean_object* v___x_908_; 
v_levelMap_906_ = lean_ctor_get(v_a_873_, 2);
v_a_907_ = lean_nat_abs(v_mantissa_888_);
lean_dec(v_mantissa_888_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_906_, v_a_907_);
if (lean_obj_tag(v___x_908_) == 1)
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_907_);
lean_del_object(v___x_886_);
v_val_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_936_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_nat_abs(v_mantissa_899_);
lean_dec(v_mantissa_899_);
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_906_, v_a_913_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_913_);
lean_del_object(v___x_911_);
lean_del_object(v___x_897_);
v_val_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_926_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_Lean_Level_imax___override(v_val_909_, v_val_915_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v_a_873_);
lean_ctor_set(v___x_902_, 0, v___x_919_);
v___x_921_ = v___x_902_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_a_873_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 0, v___x_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v___x_914_);
lean_dec(v_val_909_);
lean_del_object(v___x_902_);
lean_dec_ref(v_a_873_);
v___x_927_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_928_ = l_Nat_reprFast(v_a_913_);
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
lean_dec_ref(v___x_928_);
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 18);
lean_ctor_set(v___x_911_, 0, v___x_929_);
v___x_931_ = v___x_911_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_935_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 1);
lean_ctor_set(v___x_897_, 0, v___x_931_);
v___x_933_ = v___x_897_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
lean_dec(v___x_908_);
lean_del_object(v___x_902_);
lean_dec(v_mantissa_899_);
lean_dec_ref(v_a_873_);
v___x_937_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_938_ = l_Nat_reprFast(v_a_907_);
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
lean_dec_ref(v___x_938_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 18);
lean_ctor_set(v___x_897_, 0, v___x_939_);
v___x_941_ = v___x_897_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 1);
lean_ctor_set(v___x_886_, 0, v___x_941_);
v___x_943_ = v___x_886_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
else
{
lean_del_object(v___x_902_);
lean_dec(v_exponent_900_);
lean_dec(v_mantissa_899_);
lean_del_object(v___x_897_);
lean_dec(v_mantissa_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
}
}
}
else
{
lean_dec(v___x_894_);
lean_dec(v_mantissa_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
}
}
else
{
lean_dec(v_exponent_889_);
lean_dec(v_mantissa_888_);
lean_del_object(v___x_886_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
}
}
else
{
lean_dec(v___x_883_);
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
}
}
else
{
lean_dec_ref(v_a_873_);
goto v___jp_875_;
}
v___jp_875_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1));
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___boxed(lean_object* v_json_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_json_949_, v_a_950_);
lean_dec(v_json_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(lean_object* v_json_956_, lean_object* v_a_957_){
_start:
{
if (lean_obj_tag(v_json_956_) == 2)
{
lean_object* v_n_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_998_; 
v_n_962_ = lean_ctor_get(v_json_956_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_json_956_);
if (v_isSharedCheck_998_ == 0)
{
v___x_964_ = v_json_956_;
v_isShared_965_ = v_isSharedCheck_998_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_n_962_);
lean_dec(v_json_956_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_998_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_mantissa_966_; lean_object* v_exponent_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_997_; 
v_mantissa_966_ = lean_ctor_get(v_n_962_, 0);
v_exponent_967_ = lean_ctor_get(v_n_962_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_n_962_);
if (v_isSharedCheck_997_ == 0)
{
v___x_969_ = v_n_962_;
v_isShared_970_ = v_isSharedCheck_997_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_exponent_967_);
lean_inc(v_mantissa_966_);
lean_dec(v_n_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_997_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_natZero_971_; lean_object* v_intZero_972_; uint8_t v_isNeg_973_; 
v_natZero_971_ = lean_unsigned_to_nat(0u);
v_intZero_972_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_973_ = lean_int_dec_lt(v_mantissa_966_, v_intZero_972_);
if (v_isNeg_973_ == 0)
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_eq(v_exponent_967_, v_natZero_971_);
lean_dec(v_exponent_967_);
if (v___x_974_ == 0)
{
lean_del_object(v___x_969_);
lean_dec(v_mantissa_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_a_957_);
goto v___jp_959_;
}
else
{
lean_object* v_nameMap_975_; lean_object* v_a_976_; lean_object* v___x_977_; 
v_nameMap_975_ = lean_ctor_get(v_a_957_, 1);
v_a_976_ = lean_nat_abs(v_mantissa_966_);
lean_dec(v_mantissa_966_);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_975_, v_a_976_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_976_);
lean_del_object(v___x_964_);
v_val_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_989_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_val_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_Level_param___override(v_val_978_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_a_957_);
lean_ctor_set(v___x_969_, 0, v___x_982_);
v___x_984_ = v___x_969_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_a_957_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
lean_ctor_set(v___x_980_, 0, v___x_984_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
lean_dec(v___x_977_);
lean_del_object(v___x_969_);
lean_dec_ref(v_a_957_);
v___x_990_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_991_ = l_Nat_reprFast(v_a_976_);
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
lean_dec_ref(v___x_991_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 18);
lean_ctor_set(v___x_964_, 0, v___x_992_);
v___x_994_ = v___x_964_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
}
else
{
lean_del_object(v___x_969_);
lean_dec(v_exponent_967_);
lean_dec(v_mantissa_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_a_957_);
goto v___jp_959_;
}
}
}
}
else
{
lean_dec_ref(v_a_957_);
lean_dec(v_json_956_);
goto v___jp_959_;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1));
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___boxed(lean_object* v_json_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_json_999_, v_a_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(lean_object* v_json_1006_, lean_object* v_a_1007_){
_start:
{
if (lean_obj_tag(v_json_1006_) == 2)
{
lean_object* v_n_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1034_; 
v_n_1012_ = lean_ctor_get(v_json_1006_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_json_1006_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1014_ = v_json_1006_;
v_isShared_1015_ = v_isSharedCheck_1034_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_n_1012_);
lean_dec(v_json_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1034_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_mantissa_1016_; lean_object* v_exponent_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1033_; 
v_mantissa_1016_ = lean_ctor_get(v_n_1012_, 0);
v_exponent_1017_ = lean_ctor_get(v_n_1012_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_n_1012_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1019_ = v_n_1012_;
v_isShared_1020_ = v_isSharedCheck_1033_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_exponent_1017_);
lean_inc(v_mantissa_1016_);
lean_dec(v_n_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1033_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_natZero_1021_; lean_object* v_intZero_1022_; uint8_t v_isNeg_1023_; 
v_natZero_1021_ = lean_unsigned_to_nat(0u);
v_intZero_1022_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1023_ = lean_int_dec_lt(v_mantissa_1016_, v_intZero_1022_);
if (v_isNeg_1023_ == 0)
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_nat_dec_eq(v_exponent_1017_, v_natZero_1021_);
lean_dec(v_exponent_1017_);
if (v___x_1024_ == 0)
{
lean_del_object(v___x_1019_);
lean_dec(v_mantissa_1016_);
lean_del_object(v___x_1014_);
lean_dec_ref(v_a_1007_);
goto v___jp_1009_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v_a_1025_ = lean_nat_abs(v_mantissa_1016_);
lean_dec(v_mantissa_1016_);
v___x_1026_ = l_Lean_Expr_bvar___override(v_a_1025_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1007_);
lean_ctor_set(v___x_1019_, 0, v___x_1026_);
v___x_1028_ = v___x_1019_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_a_1007_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1028_);
v___x_1030_ = v___x_1014_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_del_object(v___x_1019_);
lean_dec(v_exponent_1017_);
lean_dec(v_mantissa_1016_);
lean_del_object(v___x_1014_);
lean_dec_ref(v_a_1007_);
goto v___jp_1009_;
}
}
}
}
else
{
lean_dec_ref(v_a_1007_);
lean_dec(v_json_1006_);
goto v___jp_1009_;
}
v___jp_1009_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1));
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___boxed(lean_object* v_json_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_json_1035_, v_a_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(lean_object* v_json_1042_, lean_object* v_a_1043_){
_start:
{
if (lean_obj_tag(v_json_1042_) == 2)
{
lean_object* v_n_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1084_; 
v_n_1048_ = lean_ctor_get(v_json_1042_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_json_1042_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1050_ = v_json_1042_;
v_isShared_1051_ = v_isSharedCheck_1084_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_n_1048_);
lean_dec(v_json_1042_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1084_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_mantissa_1052_; lean_object* v_exponent_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1083_; 
v_mantissa_1052_ = lean_ctor_get(v_n_1048_, 0);
v_exponent_1053_ = lean_ctor_get(v_n_1048_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_n_1048_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1055_ = v_n_1048_;
v_isShared_1056_ = v_isSharedCheck_1083_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_exponent_1053_);
lean_inc(v_mantissa_1052_);
lean_dec(v_n_1048_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1083_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_natZero_1057_; lean_object* v_intZero_1058_; uint8_t v_isNeg_1059_; 
v_natZero_1057_ = lean_unsigned_to_nat(0u);
v_intZero_1058_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1059_ = lean_int_dec_lt(v_mantissa_1052_, v_intZero_1058_);
if (v_isNeg_1059_ == 0)
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_eq(v_exponent_1053_, v_natZero_1057_);
lean_dec(v_exponent_1053_);
if (v___x_1060_ == 0)
{
lean_del_object(v___x_1055_);
lean_dec(v_mantissa_1052_);
lean_del_object(v___x_1050_);
lean_dec_ref(v_a_1043_);
goto v___jp_1045_;
}
else
{
lean_object* v_levelMap_1061_; lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_levelMap_1061_ = lean_ctor_get(v_a_1043_, 2);
v_a_1062_ = lean_nat_abs(v_mantissa_1052_);
lean_dec(v_mantissa_1052_);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1063_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1062_);
lean_del_object(v___x_1050_);
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_Expr_sort___override(v_val_1064_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v_a_1043_);
lean_ctor_set(v___x_1055_, 0, v___x_1068_);
v___x_1070_ = v___x_1055_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1043_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_dec(v___x_1063_);
lean_del_object(v___x_1055_);
lean_dec_ref(v_a_1043_);
v___x_1076_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1077_ = l_Nat_reprFast(v_a_1062_);
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
lean_dec_ref(v___x_1077_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 18);
lean_ctor_set(v___x_1050_, 0, v___x_1078_);
v___x_1080_ = v___x_1050_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
}
else
{
lean_del_object(v___x_1055_);
lean_dec(v_exponent_1053_);
lean_dec(v_mantissa_1052_);
lean_del_object(v___x_1050_);
lean_dec_ref(v_a_1043_);
goto v___jp_1045_;
}
}
}
}
else
{
lean_dec_ref(v_a_1043_);
lean_dec(v_json_1042_);
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1));
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___boxed(lean_object* v_json_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_json_1085_, v_a_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_bs_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_bs_1094_);
lean_ctor_set(v___x_1101_, 1, v___y_1095_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v_v_1103_; 
v_v_1103_ = lean_array_uget(v_bs_1094_, v_i_1093_);
if (lean_obj_tag(v_v_1103_) == 2)
{
lean_object* v_n_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1130_; 
v_n_1104_ = lean_ctor_get(v_v_1103_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_v_1103_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1106_ = v_v_1103_;
v_isShared_1107_ = v_isSharedCheck_1130_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_n_1104_);
lean_dec(v_v_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1130_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_mantissa_1108_; lean_object* v_exponent_1109_; lean_object* v_natZero_1110_; lean_object* v_intZero_1111_; uint8_t v_isNeg_1112_; 
v_mantissa_1108_ = lean_ctor_get(v_n_1104_, 0);
lean_inc(v_mantissa_1108_);
v_exponent_1109_ = lean_ctor_get(v_n_1104_, 1);
lean_inc(v_exponent_1109_);
lean_dec_ref(v_n_1104_);
v_natZero_1110_ = lean_unsigned_to_nat(0u);
v_intZero_1111_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1112_ = lean_int_dec_lt(v_mantissa_1108_, v_intZero_1111_);
if (v_isNeg_1112_ == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_nat_dec_eq(v_exponent_1109_, v_natZero_1110_);
lean_dec(v_exponent_1109_);
if (v___x_1113_ == 0)
{
lean_dec(v_mantissa_1108_);
lean_del_object(v___x_1106_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_bs_1094_);
goto v___jp_1097_;
}
else
{
lean_object* v_levelMap_1114_; lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_levelMap_1114_ = lean_ctor_get(v___y_1095_, 2);
v_a_1115_ = lean_nat_abs(v_mantissa_1108_);
lean_dec(v_mantissa_1108_);
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1116_) == 1)
{
lean_object* v_val_1117_; lean_object* v_bs_x27_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_a_1115_);
lean_del_object(v___x_1106_);
v_val_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v_bs_x27_1118_ = lean_array_uset(v_bs_1094_, v_i_1093_, v_natZero_1110_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1093_, v___x_1119_);
v___x_1121_ = lean_array_uset(v_bs_x27_1118_, v_i_1093_, v_val_1117_);
v_i_1093_ = v___x_1120_;
v_bs_1094_ = v___x_1121_;
goto _start;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec(v___x_1116_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_bs_1094_);
v___x_1123_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1124_ = l_Nat_reprFast(v_a_1115_);
v___x_1125_ = lean_string_append(v___x_1123_, v___x_1124_);
lean_dec_ref(v___x_1124_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 18);
lean_ctor_set(v___x_1106_, 0, v___x_1125_);
v___x_1127_ = v___x_1106_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
}
}
else
{
lean_dec(v_exponent_1109_);
lean_dec(v_mantissa_1108_);
lean_del_object(v___x_1106_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_bs_1094_);
goto v___jp_1097_;
}
}
}
else
{
lean_dec(v_v_1103_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_bs_1094_);
goto v___jp_1097_;
}
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___boxed(lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_bs_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_boxed_1136_, v_i_boxed_1137_, v_bs_1133_, v___y_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(lean_object* v_json_1141_, lean_object* v_a_1142_){
_start:
{
if (lean_obj_tag(v_json_1141_) == 5)
{
lean_object* v_kvPairs_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_kvPairs_1150_ = lean_ctor_get(v_json_1141_, 0);
v___x_1151_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1150_, v___x_1151_);
if (lean_obj_tag(v___x_1152_) == 1)
{
lean_object* v_val_1153_; 
v_val_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1152_, 1);
if (lean_obj_tag(v_val_1153_) == 2)
{
lean_object* v_n_1154_; lean_object* v_mantissa_1155_; lean_object* v_exponent_1156_; lean_object* v_natZero_1157_; lean_object* v_intZero_1158_; uint8_t v_isNeg_1159_; 
v_n_1154_ = lean_ctor_get(v_val_1153_, 0);
lean_inc_ref(v_n_1154_);
lean_dec_ref_known(v_val_1153_, 1);
v_mantissa_1155_ = lean_ctor_get(v_n_1154_, 0);
lean_inc(v_mantissa_1155_);
v_exponent_1156_ = lean_ctor_get(v_n_1154_, 1);
lean_inc(v_exponent_1156_);
lean_dec_ref(v_n_1154_);
v_natZero_1157_ = lean_unsigned_to_nat(0u);
v_intZero_1158_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1159_ = lean_int_dec_lt(v_mantissa_1155_, v_intZero_1158_);
if (v_isNeg_1159_ == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_eq(v_exponent_1156_, v_natZero_1157_);
lean_dec(v_exponent_1156_);
if (v___x_1160_ == 0)
{
lean_dec(v_mantissa_1155_);
lean_dec_ref(v_a_1142_);
goto v___jp_1144_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1));
v___x_1162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1150_, v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 1)
{
lean_object* v_val_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1215_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1215_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_val_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1215_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
if (lean_obj_tag(v_val_1163_) == 4)
{
lean_object* v_elems_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1214_; 
v_elems_1167_ = lean_ctor_get(v_val_1163_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_val_1163_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1169_ = v_val_1163_;
v_isShared_1170_ = v_isSharedCheck_1214_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_elems_1167_);
lean_dec(v_val_1163_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1214_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_nameMap_1171_; lean_object* v_a_1172_; lean_object* v___x_1173_; 
v_nameMap_1171_ = lean_ctor_get(v_a_1142_, 1);
v_a_1172_ = lean_nat_abs(v_mantissa_1155_);
lean_dec(v_mantissa_1155_);
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1173_) == 1)
{
lean_object* v_val_1174_; size_t v_sz_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v_a_1172_);
lean_del_object(v___x_1169_);
lean_del_object(v___x_1165_);
v_val_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_val_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v_sz_1175_ = lean_array_size(v_elems_1167_);
v___x_1176_ = ((size_t)0ULL);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_1175_, v___x_1176_, v_elems_1167_, v_a_1142_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1196_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1196_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1196_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1195_; 
v_fst_1182_ = lean_ctor_get(v_a_1178_, 0);
v_snd_1183_ = lean_ctor_get(v_a_1178_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1178_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1185_ = v_a_1178_;
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_inc(v_fst_1182_);
lean_dec(v_a_1178_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_array_to_list(v_fst_1182_);
v___x_1188_ = l_Lean_Expr_const___override(v_val_1174_, v___x_1187_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_snd_1183_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1190_);
v___x_1192_ = v___x_1180_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_val_1174_);
v_a_1197_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1177_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1177_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec(v___x_1173_);
lean_dec_ref(v_elems_1167_);
lean_dec_ref(v_a_1142_);
v___x_1205_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1206_ = l_Nat_reprFast(v_a_1172_);
v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
lean_dec_ref(v___x_1206_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 18);
lean_ctor_set(v___x_1169_, 0, v___x_1207_);
v___x_1209_ = v___x_1169_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1209_);
v___x_1211_ = v___x_1165_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
else
{
lean_del_object(v___x_1165_);
lean_dec(v_val_1163_);
lean_dec(v_mantissa_1155_);
lean_dec_ref(v_a_1142_);
goto v___jp_1147_;
}
}
}
else
{
lean_dec(v___x_1162_);
lean_dec(v_mantissa_1155_);
lean_dec_ref(v_a_1142_);
goto v___jp_1147_;
}
}
}
else
{
lean_dec(v_exponent_1156_);
lean_dec(v_mantissa_1155_);
lean_dec_ref(v_a_1142_);
goto v___jp_1144_;
}
}
else
{
lean_dec(v_val_1153_);
lean_dec_ref(v_a_1142_);
goto v___jp_1144_;
}
}
else
{
lean_dec(v___x_1152_);
lean_dec_ref(v_a_1142_);
goto v___jp_1144_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_a_1142_);
v___x_1216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
v___jp_1147_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___boxed(lean_object* v_json_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_json_1218_, v_a_1219_);
lean_dec(v_json_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(lean_object* v_json_1227_, lean_object* v_a_1228_){
_start:
{
if (lean_obj_tag(v_json_1227_) == 5)
{
lean_object* v_kvPairs_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_kvPairs_1236_ = lean_ctor_get(v_json_1227_, 0);
v___x_1237_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2));
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1236_, v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 1)
{
lean_object* v_val_1239_; 
v_val_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v___x_1238_, 1);
if (lean_obj_tag(v_val_1239_) == 2)
{
lean_object* v_n_1240_; lean_object* v_mantissa_1241_; lean_object* v_exponent_1242_; lean_object* v_natZero_1243_; lean_object* v_intZero_1244_; uint8_t v_isNeg_1245_; 
v_n_1240_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_n_1240_);
lean_dec_ref_known(v_val_1239_, 1);
v_mantissa_1241_ = lean_ctor_get(v_n_1240_, 0);
lean_inc(v_mantissa_1241_);
v_exponent_1242_ = lean_ctor_get(v_n_1240_, 1);
lean_inc(v_exponent_1242_);
lean_dec_ref(v_n_1240_);
v_natZero_1243_ = lean_unsigned_to_nat(0u);
v_intZero_1244_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1245_ = lean_int_dec_lt(v_mantissa_1241_, v_intZero_1244_);
if (v_isNeg_1245_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_nat_dec_eq(v_exponent_1242_, v_natZero_1243_);
lean_dec(v_exponent_1242_);
if (v___x_1246_ == 0)
{
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3));
v___x_1248_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1236_, v___x_1247_);
if (lean_obj_tag(v___x_1248_) == 1)
{
lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1306_; 
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1306_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1306_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
if (lean_obj_tag(v_val_1249_) == 2)
{
lean_object* v_n_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1305_; 
v_n_1253_ = lean_ctor_get(v_val_1249_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_val_1249_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1255_ = v_val_1249_;
v_isShared_1256_ = v_isSharedCheck_1305_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_n_1253_);
lean_dec(v_val_1249_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1305_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_mantissa_1257_; lean_object* v_exponent_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1304_; 
v_mantissa_1257_ = lean_ctor_get(v_n_1253_, 0);
v_exponent_1258_ = lean_ctor_get(v_n_1253_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_n_1253_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1260_ = v_n_1253_;
v_isShared_1261_ = v_isSharedCheck_1304_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_exponent_1258_);
lean_inc(v_mantissa_1257_);
lean_dec(v_n_1253_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1304_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
uint8_t v_isNeg_1262_; 
v_isNeg_1262_ = lean_int_dec_lt(v_mantissa_1257_, v_intZero_1244_);
if (v_isNeg_1262_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_eq(v_exponent_1258_, v_natZero_1243_);
lean_dec(v_exponent_1258_);
if (v___x_1263_ == 0)
{
lean_del_object(v___x_1260_);
lean_dec(v_mantissa_1257_);
lean_del_object(v___x_1255_);
lean_del_object(v___x_1251_);
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1233_;
}
else
{
lean_object* v_exprMap_1264_; lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_exprMap_1264_ = lean_ctor_get(v_a_1228_, 3);
v_a_1265_ = lean_nat_abs(v_mantissa_1241_);
lean_dec(v_mantissa_1241_);
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1264_, v_a_1265_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1265_);
lean_del_object(v___x_1251_);
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1294_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1294_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_nat_abs(v_mantissa_1257_);
lean_dec(v_mantissa_1257_);
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1264_, v_a_1271_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_a_1271_);
lean_del_object(v___x_1269_);
lean_del_object(v___x_1255_);
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = l_Lean_Expr_app___override(v_val_1267_, v_val_1273_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_a_1228_);
lean_ctor_set(v___x_1260_, 0, v___x_1277_);
v___x_1279_ = v___x_1260_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1228_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 0);
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
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v___x_1272_);
lean_dec(v_val_1267_);
lean_del_object(v___x_1260_);
lean_dec_ref(v_a_1228_);
v___x_1285_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1286_ = l_Nat_reprFast(v_a_1271_);
v___x_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
lean_dec_ref(v___x_1286_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 18);
lean_ctor_set(v___x_1269_, 0, v___x_1287_);
v___x_1289_ = v___x_1269_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 0, v___x_1289_);
v___x_1291_ = v___x_1255_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec(v___x_1266_);
lean_del_object(v___x_1260_);
lean_dec(v_mantissa_1257_);
lean_dec_ref(v_a_1228_);
v___x_1295_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1296_ = l_Nat_reprFast(v_a_1265_);
v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
lean_dec_ref(v___x_1296_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 18);
lean_ctor_set(v___x_1255_, 0, v___x_1297_);
v___x_1299_ = v___x_1255_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1299_);
v___x_1301_ = v___x_1251_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_del_object(v___x_1260_);
lean_dec(v_exponent_1258_);
lean_dec(v_mantissa_1257_);
lean_del_object(v___x_1255_);
lean_del_object(v___x_1251_);
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1233_;
}
}
}
}
else
{
lean_del_object(v___x_1251_);
lean_dec(v_val_1249_);
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1233_;
}
}
}
else
{
lean_dec(v___x_1248_);
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1233_;
}
}
}
else
{
lean_dec(v_exponent_1242_);
lean_dec(v_mantissa_1241_);
lean_dec_ref(v_a_1228_);
goto v___jp_1230_;
}
}
else
{
lean_dec(v_val_1239_);
lean_dec_ref(v_a_1228_);
goto v___jp_1230_;
}
}
else
{
lean_dec(v___x_1238_);
lean_dec_ref(v_a_1228_);
goto v___jp_1230_;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v_a_1228_);
v___x_1307_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
v___jp_1230_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
v___jp_1233_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___boxed(lean_object* v_json_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_json_1309_, v_a_1310_);
lean_dec(v_json_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(lean_object* v_info_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0));
v___x_1322_ = lean_string_dec_eq(v_info_1318_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1));
v___x_1324_ = lean_string_dec_eq(v_info_1318_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2));
v___x_1326_ = lean_string_dec_eq(v_info_1318_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3));
v___x_1328_ = lean_string_dec_eq(v_info_1318_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_a_1319_);
v___x_1329_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4));
v___x_1330_ = lean_string_append(v___x_1329_, v_info_1318_);
v___x_1331_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
else
{
uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = 3;
v___x_1334_ = lean_box(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_a_1319_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
else
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = 2;
v___x_1338_ = lean_box(v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_a_1319_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
else
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1341_ = 1;
v___x_1342_ = lean_box(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_a_1319_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
else
{
uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = 0;
v___x_1346_ = lean_box(v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_a_1319_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___boxed(lean_object* v_info_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_info_1349_, v_a_1350_);
lean_dec_ref(v_info_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(lean_object* v_json_1359_, lean_object* v_a_1360_){
_start:
{
if (lean_obj_tag(v_json_1359_) == 5)
{
lean_object* v_kvPairs_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_kvPairs_1374_ = lean_ctor_get(v_json_1359_, 0);
v___x_1375_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1374_, v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_val_1377_) == 2)
{
lean_object* v_n_1378_; lean_object* v_mantissa_1379_; lean_object* v_exponent_1380_; lean_object* v_natZero_1381_; lean_object* v_intZero_1382_; uint8_t v_isNeg_1383_; 
v_n_1378_ = lean_ctor_get(v_val_1377_, 0);
lean_inc_ref(v_n_1378_);
lean_dec_ref_known(v_val_1377_, 1);
v_mantissa_1379_ = lean_ctor_get(v_n_1378_, 0);
lean_inc(v_mantissa_1379_);
v_exponent_1380_ = lean_ctor_get(v_n_1378_, 1);
lean_inc(v_exponent_1380_);
lean_dec_ref(v_n_1378_);
v_natZero_1381_ = lean_unsigned_to_nat(0u);
v_intZero_1382_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1383_ = lean_int_dec_lt(v_mantissa_1379_, v_intZero_1382_);
if (v_isNeg_1383_ == 0)
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_eq(v_exponent_1380_, v_natZero_1381_);
lean_dec(v_exponent_1380_);
if (v___x_1384_ == 0)
{
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1362_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1374_, v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 1)
{
lean_object* v_val_1387_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1387_);
lean_dec_ref_known(v___x_1386_, 1);
if (lean_obj_tag(v_val_1387_) == 2)
{
lean_object* v_n_1388_; lean_object* v_mantissa_1389_; lean_object* v_exponent_1390_; uint8_t v_isNeg_1391_; 
v_n_1388_ = lean_ctor_get(v_val_1387_, 0);
lean_inc_ref(v_n_1388_);
lean_dec_ref_known(v_val_1387_, 1);
v_mantissa_1389_ = lean_ctor_get(v_n_1388_, 0);
lean_inc(v_mantissa_1389_);
v_exponent_1390_ = lean_ctor_get(v_n_1388_, 1);
lean_inc(v_exponent_1390_);
lean_dec_ref(v_n_1388_);
v_isNeg_1391_ = lean_int_dec_lt(v_mantissa_1389_, v_intZero_1382_);
if (v_isNeg_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_eq(v_exponent_1390_, v_natZero_1381_);
lean_dec(v_exponent_1390_);
if (v___x_1392_ == 0)
{
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1365_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1374_, v___x_1393_);
if (lean_obj_tag(v___x_1394_) == 1)
{
lean_object* v_val_1395_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1394_, 1);
if (lean_obj_tag(v_val_1395_) == 2)
{
lean_object* v_n_1396_; lean_object* v_mantissa_1397_; lean_object* v_exponent_1398_; uint8_t v_isNeg_1399_; 
v_n_1396_ = lean_ctor_get(v_val_1395_, 0);
lean_inc_ref(v_n_1396_);
lean_dec_ref_known(v_val_1395_, 1);
v_mantissa_1397_ = lean_ctor_get(v_n_1396_, 0);
lean_inc(v_mantissa_1397_);
v_exponent_1398_ = lean_ctor_get(v_n_1396_, 1);
lean_inc(v_exponent_1398_);
lean_dec_ref(v_n_1396_);
v_isNeg_1399_ = lean_int_dec_lt(v_mantissa_1397_, v_intZero_1382_);
if (v_isNeg_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_eq(v_exponent_1398_, v_natZero_1381_);
lean_dec(v_exponent_1398_);
if (v___x_1400_ == 0)
{
lean_dec(v_mantissa_1397_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1368_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1374_, v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 1)
{
lean_object* v_val_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1486_; 
v_val_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1486_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_val_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1486_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
if (lean_obj_tag(v_val_1403_) == 3)
{
lean_object* v_s_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1485_; 
v_s_1407_ = lean_ctor_get(v_val_1403_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_val_1403_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1409_ = v_val_1403_;
v_isShared_1410_ = v_isSharedCheck_1485_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_s_1407_);
lean_dec(v_val_1403_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1485_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_nameMap_1411_; lean_object* v_exprMap_1412_; lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_nameMap_1411_ = lean_ctor_get(v_a_1360_, 1);
v_exprMap_1412_ = lean_ctor_get(v_a_1360_, 3);
v_a_1413_ = lean_nat_abs(v_mantissa_1379_);
lean_dec(v_mantissa_1379_);
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1411_, v_a_1413_);
if (lean_obj_tag(v___x_1414_) == 1)
{
lean_object* v_val_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1413_);
lean_del_object(v___x_1405_);
v_val_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1475_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_val_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1475_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_nat_abs(v_mantissa_1389_);
lean_dec(v_mantissa_1389_);
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1412_, v_a_1419_);
if (lean_obj_tag(v___x_1420_) == 1)
{
lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1419_);
lean_del_object(v___x_1409_);
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1465_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1465_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_nat_abs(v_mantissa_1397_);
lean_dec(v_mantissa_1397_);
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1412_, v_a_1425_);
if (lean_obj_tag(v___x_1426_) == 1)
{
lean_object* v_val_1427_; lean_object* v___x_1428_; 
lean_dec(v_a_1425_);
lean_del_object(v___x_1423_);
lean_del_object(v___x_1417_);
v_val_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1407_, v_a_1360_);
lean_dec_ref(v_s_1407_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1447_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
v_fst_1433_ = lean_ctor_get(v_a_1429_, 0);
v_snd_1434_ = lean_ctor_get(v_a_1429_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v_a_1429_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_inc(v_fst_1433_);
lean_dec(v_a_1429_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = lean_unbox(v_fst_1433_);
lean_dec(v_fst_1433_);
v___x_1439_ = l_Lean_Expr_lam___override(v_val_1415_, v_val_1421_, v_val_1427_, v___x_1438_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_snd_1434_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1441_);
v___x_1443_ = v___x_1431_;
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
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_val_1427_);
lean_dec(v_val_1421_);
lean_dec(v_val_1415_);
v_a_1448_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1428_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1428_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec(v___x_1426_);
lean_dec(v_val_1421_);
lean_dec(v_val_1415_);
lean_dec_ref(v_s_1407_);
lean_dec_ref(v_a_1360_);
v___x_1456_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1457_ = l_Nat_reprFast(v_a_1425_);
v___x_1458_ = lean_string_append(v___x_1456_, v___x_1457_);
lean_dec_ref(v___x_1457_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 18);
lean_ctor_set(v___x_1423_, 0, v___x_1458_);
v___x_1460_ = v___x_1423_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1460_);
v___x_1462_ = v___x_1417_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v___x_1420_);
lean_dec(v_val_1415_);
lean_dec_ref(v_s_1407_);
lean_dec(v_mantissa_1397_);
lean_dec_ref(v_a_1360_);
v___x_1466_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1467_ = l_Nat_reprFast(v_a_1419_);
v___x_1468_ = lean_string_append(v___x_1466_, v___x_1467_);
lean_dec_ref(v___x_1467_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 18);
lean_ctor_set(v___x_1417_, 0, v___x_1468_);
v___x_1470_ = v___x_1417_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 1);
lean_ctor_set(v___x_1409_, 0, v___x_1470_);
v___x_1472_ = v___x_1409_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v___x_1414_);
lean_dec_ref(v_s_1407_);
lean_dec(v_mantissa_1397_);
lean_dec(v_mantissa_1389_);
lean_dec_ref(v_a_1360_);
v___x_1476_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1477_ = l_Nat_reprFast(v_a_1413_);
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
lean_dec_ref(v___x_1477_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 18);
lean_ctor_set(v___x_1409_, 0, v___x_1478_);
v___x_1480_ = v___x_1409_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1480_);
v___x_1482_ = v___x_1405_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
else
{
lean_del_object(v___x_1405_);
lean_dec(v_val_1403_);
lean_dec(v_mantissa_1397_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1371_;
}
}
}
else
{
lean_dec(v___x_1402_);
lean_dec(v_mantissa_1397_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1371_;
}
}
}
else
{
lean_dec(v_exponent_1398_);
lean_dec(v_mantissa_1397_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1368_;
}
}
else
{
lean_dec(v_val_1395_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1368_;
}
}
else
{
lean_dec(v___x_1394_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1368_;
}
}
}
else
{
lean_dec(v_exponent_1390_);
lean_dec(v_mantissa_1389_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1365_;
}
}
else
{
lean_dec(v_val_1387_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1365_;
}
}
else
{
lean_dec(v___x_1386_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1365_;
}
}
}
else
{
lean_dec(v_exponent_1380_);
lean_dec(v_mantissa_1379_);
lean_dec_ref(v_a_1360_);
goto v___jp_1362_;
}
}
else
{
lean_dec(v_val_1377_);
lean_dec_ref(v_a_1360_);
goto v___jp_1362_;
}
}
else
{
lean_dec(v___x_1376_);
lean_dec_ref(v_a_1360_);
goto v___jp_1362_;
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v_a_1360_);
v___x_1487_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
v___jp_1362_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
v___jp_1365_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
v___jp_1368_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
v___jp_1371_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___boxed(lean_object* v_json_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_json_1489_, v_a_1490_);
lean_dec(v_json_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(lean_object* v_json_1496_, lean_object* v_a_1497_){
_start:
{
if (lean_obj_tag(v_json_1496_) == 5)
{
lean_object* v_kvPairs_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_kvPairs_1511_ = lean_ctor_get(v_json_1496_, 0);
v___x_1512_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1511_, v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 1)
{
lean_object* v_val_1514_; 
v_val_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1513_, 1);
if (lean_obj_tag(v_val_1514_) == 2)
{
lean_object* v_n_1515_; lean_object* v_mantissa_1516_; lean_object* v_exponent_1517_; lean_object* v_natZero_1518_; lean_object* v_intZero_1519_; uint8_t v_isNeg_1520_; 
v_n_1515_ = lean_ctor_get(v_val_1514_, 0);
lean_inc_ref(v_n_1515_);
lean_dec_ref_known(v_val_1514_, 1);
v_mantissa_1516_ = lean_ctor_get(v_n_1515_, 0);
lean_inc(v_mantissa_1516_);
v_exponent_1517_ = lean_ctor_get(v_n_1515_, 1);
lean_inc(v_exponent_1517_);
lean_dec_ref(v_n_1515_);
v_natZero_1518_ = lean_unsigned_to_nat(0u);
v_intZero_1519_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1520_ = lean_int_dec_lt(v_mantissa_1516_, v_intZero_1519_);
if (v_isNeg_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_nat_dec_eq(v_exponent_1517_, v_natZero_1518_);
lean_dec(v_exponent_1517_);
if (v___x_1521_ == 0)
{
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1511_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 1)
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v___x_1523_, 1);
if (lean_obj_tag(v_val_1524_) == 2)
{
lean_object* v_n_1525_; lean_object* v_mantissa_1526_; lean_object* v_exponent_1527_; uint8_t v_isNeg_1528_; 
v_n_1525_ = lean_ctor_get(v_val_1524_, 0);
lean_inc_ref(v_n_1525_);
lean_dec_ref_known(v_val_1524_, 1);
v_mantissa_1526_ = lean_ctor_get(v_n_1525_, 0);
lean_inc(v_mantissa_1526_);
v_exponent_1527_ = lean_ctor_get(v_n_1525_, 1);
lean_inc(v_exponent_1527_);
lean_dec_ref(v_n_1525_);
v_isNeg_1528_ = lean_int_dec_lt(v_mantissa_1526_, v_intZero_1519_);
if (v_isNeg_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_nat_dec_eq(v_exponent_1527_, v_natZero_1518_);
lean_dec(v_exponent_1527_);
if (v___x_1529_ == 0)
{
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1502_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1531_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1511_, v___x_1530_);
if (lean_obj_tag(v___x_1531_) == 1)
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1531_, 1);
if (lean_obj_tag(v_val_1532_) == 2)
{
lean_object* v_n_1533_; lean_object* v_mantissa_1534_; lean_object* v_exponent_1535_; uint8_t v_isNeg_1536_; 
v_n_1533_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_n_1533_);
lean_dec_ref_known(v_val_1532_, 1);
v_mantissa_1534_ = lean_ctor_get(v_n_1533_, 0);
lean_inc(v_mantissa_1534_);
v_exponent_1535_ = lean_ctor_get(v_n_1533_, 1);
lean_inc(v_exponent_1535_);
lean_dec_ref(v_n_1533_);
v_isNeg_1536_ = lean_int_dec_lt(v_mantissa_1534_, v_intZero_1519_);
if (v_isNeg_1536_ == 0)
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_nat_dec_eq(v_exponent_1535_, v_natZero_1518_);
lean_dec(v_exponent_1535_);
if (v___x_1537_ == 0)
{
lean_dec(v_mantissa_1534_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1505_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1511_, v___x_1538_);
if (lean_obj_tag(v___x_1539_) == 1)
{
lean_object* v_val_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1623_; 
v_val_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1623_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_val_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1623_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
if (lean_obj_tag(v_val_1540_) == 3)
{
lean_object* v_s_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1622_; 
v_s_1544_ = lean_ctor_get(v_val_1540_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_val_1540_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1546_ = v_val_1540_;
v_isShared_1547_ = v_isSharedCheck_1622_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_s_1544_);
lean_dec(v_val_1540_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1622_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_nameMap_1548_; lean_object* v_exprMap_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_nameMap_1548_ = lean_ctor_get(v_a_1497_, 1);
v_exprMap_1549_ = lean_ctor_get(v_a_1497_, 3);
v_a_1550_ = lean_nat_abs(v_mantissa_1516_);
lean_dec(v_mantissa_1516_);
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1548_, v_a_1550_);
if (lean_obj_tag(v___x_1551_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1550_);
lean_del_object(v___x_1542_);
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1612_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1612_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_nat_abs(v_mantissa_1526_);
lean_dec(v_mantissa_1526_);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1549_, v_a_1556_);
if (lean_obj_tag(v___x_1557_) == 1)
{
lean_object* v_val_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1556_);
lean_del_object(v___x_1546_);
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1602_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_val_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1602_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_nat_abs(v_mantissa_1534_);
lean_dec(v_mantissa_1534_);
v___x_1563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1549_, v_a_1562_);
if (lean_obj_tag(v___x_1563_) == 1)
{
lean_object* v_val_1564_; lean_object* v___x_1565_; 
lean_dec(v_a_1562_);
lean_del_object(v___x_1560_);
lean_del_object(v___x_1554_);
v_val_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1544_, v_a_1497_);
lean_dec_ref(v_s_1544_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1584_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1584_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1584_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1583_; 
v_fst_1570_ = lean_ctor_get(v_a_1566_, 0);
v_snd_1571_ = lean_ctor_get(v_a_1566_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_a_1566_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1573_ = v_a_1566_;
v_isShared_1574_ = v_isSharedCheck_1583_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_a_1566_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1583_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_unbox(v_fst_1570_);
lean_dec(v_fst_1570_);
v___x_1576_ = l_Lean_Expr_forallE___override(v_val_1552_, v_val_1558_, v_val_1564_, v___x_1575_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_snd_1571_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1578_);
v___x_1580_ = v___x_1568_;
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
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_val_1564_);
lean_dec(v_val_1558_);
lean_dec(v_val_1552_);
v_a_1585_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1565_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1565_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v___x_1563_);
lean_dec(v_val_1558_);
lean_dec(v_val_1552_);
lean_dec_ref(v_s_1544_);
lean_dec_ref(v_a_1497_);
v___x_1593_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1594_ = l_Nat_reprFast(v_a_1562_);
v___x_1595_ = lean_string_append(v___x_1593_, v___x_1594_);
lean_dec_ref(v___x_1594_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 18);
lean_ctor_set(v___x_1560_, 0, v___x_1595_);
v___x_1597_ = v___x_1560_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1597_);
v___x_1599_ = v___x_1554_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_dec(v___x_1557_);
lean_dec(v_val_1552_);
lean_dec_ref(v_s_1544_);
lean_dec(v_mantissa_1534_);
lean_dec_ref(v_a_1497_);
v___x_1603_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1604_ = l_Nat_reprFast(v_a_1556_);
v___x_1605_ = lean_string_append(v___x_1603_, v___x_1604_);
lean_dec_ref(v___x_1604_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 18);
lean_ctor_set(v___x_1554_, 0, v___x_1605_);
v___x_1607_ = v___x_1554_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1607_);
v___x_1609_ = v___x_1546_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec(v___x_1551_);
lean_dec_ref(v_s_1544_);
lean_dec(v_mantissa_1534_);
lean_dec(v_mantissa_1526_);
lean_dec_ref(v_a_1497_);
v___x_1613_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1614_ = l_Nat_reprFast(v_a_1550_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 18);
lean_ctor_set(v___x_1546_, 0, v___x_1615_);
v___x_1617_ = v___x_1546_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1617_);
v___x_1619_ = v___x_1542_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_del_object(v___x_1542_);
lean_dec(v_val_1540_);
lean_dec(v_mantissa_1534_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1508_;
}
}
}
else
{
lean_dec(v___x_1539_);
lean_dec(v_mantissa_1534_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1508_;
}
}
}
else
{
lean_dec(v_exponent_1535_);
lean_dec(v_mantissa_1534_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1505_;
}
}
else
{
lean_dec(v_val_1532_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1505_;
}
}
else
{
lean_dec(v___x_1531_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1505_;
}
}
}
else
{
lean_dec(v_exponent_1527_);
lean_dec(v_mantissa_1526_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1502_;
}
}
else
{
lean_dec(v_val_1524_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1502_;
}
}
else
{
lean_dec(v___x_1523_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1502_;
}
}
}
else
{
lean_dec(v_exponent_1517_);
lean_dec(v_mantissa_1516_);
lean_dec_ref(v_a_1497_);
goto v___jp_1499_;
}
}
else
{
lean_dec(v_val_1514_);
lean_dec_ref(v_a_1497_);
goto v___jp_1499_;
}
}
else
{
lean_dec(v___x_1513_);
lean_dec_ref(v_a_1497_);
goto v___jp_1499_;
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v_a_1497_);
v___x_1624_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
v___jp_1502_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
v___jp_1505_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
v___jp_1508_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___boxed(lean_object* v_json_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_json_1626_, v_a_1627_);
lean_dec(v_json_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(lean_object* v_json_1635_, lean_object* v_a_1636_){
_start:
{
if (lean_obj_tag(v_json_1635_) == 5)
{
lean_object* v_kvPairs_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_kvPairs_1653_ = lean_ctor_get(v_json_1635_, 0);
v___x_1654_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1653_, v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 1)
{
lean_object* v_val_1656_; 
v_val_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___x_1655_, 1);
if (lean_obj_tag(v_val_1656_) == 2)
{
lean_object* v_n_1657_; lean_object* v_mantissa_1658_; lean_object* v_exponent_1659_; lean_object* v_natZero_1660_; lean_object* v_intZero_1661_; uint8_t v_isNeg_1662_; 
v_n_1657_ = lean_ctor_get(v_val_1656_, 0);
lean_inc_ref(v_n_1657_);
lean_dec_ref_known(v_val_1656_, 1);
v_mantissa_1658_ = lean_ctor_get(v_n_1657_, 0);
lean_inc(v_mantissa_1658_);
v_exponent_1659_ = lean_ctor_get(v_n_1657_, 1);
lean_inc(v_exponent_1659_);
lean_dec_ref(v_n_1657_);
v_natZero_1660_ = lean_unsigned_to_nat(0u);
v_intZero_1661_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1662_ = lean_int_dec_lt(v_mantissa_1658_, v_intZero_1661_);
if (v_isNeg_1662_ == 0)
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_nat_dec_eq(v_exponent_1659_, v_natZero_1660_);
lean_dec(v_exponent_1659_);
if (v___x_1663_ == 0)
{
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1638_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1653_, v___x_1664_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_val_1666_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1665_, 1);
if (lean_obj_tag(v_val_1666_) == 2)
{
lean_object* v_n_1667_; lean_object* v_mantissa_1668_; lean_object* v_exponent_1669_; uint8_t v_isNeg_1670_; 
v_n_1667_ = lean_ctor_get(v_val_1666_, 0);
lean_inc_ref(v_n_1667_);
lean_dec_ref_known(v_val_1666_, 1);
v_mantissa_1668_ = lean_ctor_get(v_n_1667_, 0);
lean_inc(v_mantissa_1668_);
v_exponent_1669_ = lean_ctor_get(v_n_1667_, 1);
lean_inc(v_exponent_1669_);
lean_dec_ref(v_n_1667_);
v_isNeg_1670_ = lean_int_dec_lt(v_mantissa_1668_, v_intZero_1661_);
if (v_isNeg_1670_ == 0)
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_nat_dec_eq(v_exponent_1669_, v_natZero_1660_);
lean_dec(v_exponent_1669_);
if (v___x_1671_ == 0)
{
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1641_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1653_, v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 1)
{
lean_object* v_val_1674_; 
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___x_1673_, 1);
if (lean_obj_tag(v_val_1674_) == 2)
{
lean_object* v_n_1675_; lean_object* v_mantissa_1676_; lean_object* v_exponent_1677_; uint8_t v_isNeg_1678_; 
v_n_1675_ = lean_ctor_get(v_val_1674_, 0);
lean_inc_ref(v_n_1675_);
lean_dec_ref_known(v_val_1674_, 1);
v_mantissa_1676_ = lean_ctor_get(v_n_1675_, 0);
lean_inc(v_mantissa_1676_);
v_exponent_1677_ = lean_ctor_get(v_n_1675_, 1);
lean_inc(v_exponent_1677_);
lean_dec_ref(v_n_1675_);
v_isNeg_1678_ = lean_int_dec_lt(v_mantissa_1676_, v_intZero_1661_);
if (v_isNeg_1678_ == 0)
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_nat_dec_eq(v_exponent_1677_, v_natZero_1660_);
lean_dec(v_exponent_1677_);
if (v___x_1679_ == 0)
{
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1644_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1653_, v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 1)
{
lean_object* v_val_1682_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
if (lean_obj_tag(v_val_1682_) == 2)
{
lean_object* v_n_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1776_; 
v_n_1683_ = lean_ctor_get(v_val_1682_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_val_1682_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1685_ = v_val_1682_;
v_isShared_1686_ = v_isSharedCheck_1776_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_n_1683_);
lean_dec(v_val_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1776_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_mantissa_1687_; lean_object* v_exponent_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1775_; 
v_mantissa_1687_ = lean_ctor_get(v_n_1683_, 0);
v_exponent_1688_ = lean_ctor_get(v_n_1683_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_n_1683_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1690_ = v_n_1683_;
v_isShared_1691_ = v_isSharedCheck_1775_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_exponent_1688_);
lean_inc(v_mantissa_1687_);
lean_dec(v_n_1683_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1775_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
uint8_t v_isNeg_1692_; 
v_isNeg_1692_ = lean_int_dec_lt(v_mantissa_1687_, v_intZero_1661_);
if (v_isNeg_1692_ == 0)
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_nat_dec_eq(v_exponent_1688_, v_natZero_1660_);
lean_dec(v_exponent_1688_);
if (v___x_1693_ == 0)
{
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_del_object(v___x_1685_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1647_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3));
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1653_, v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 1)
{
lean_object* v_val_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1774_; 
v_val_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1774_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_val_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1774_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
if (lean_obj_tag(v_val_1696_) == 1)
{
uint8_t v_b_1700_; lean_object* v_nameMap_1701_; lean_object* v_exprMap_1702_; lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_b_1700_ = lean_ctor_get_uint8(v_val_1696_, 0);
lean_dec_ref_known(v_val_1696_, 0);
v_nameMap_1701_ = lean_ctor_get(v_a_1636_, 1);
v_exprMap_1702_ = lean_ctor_get(v_a_1636_, 3);
v_a_1703_ = lean_nat_abs(v_mantissa_1658_);
lean_dec(v_mantissa_1658_);
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1701_, v_a_1703_);
if (lean_obj_tag(v___x_1704_) == 1)
{
lean_object* v_val_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_a_1703_);
lean_del_object(v___x_1685_);
v_val_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1764_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_val_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1764_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_nat_abs(v_mantissa_1668_);
lean_dec(v_mantissa_1668_);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1702_, v_a_1709_);
if (lean_obj_tag(v___x_1710_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1709_);
lean_del_object(v___x_1698_);
v_val_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1754_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_val_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1754_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_nat_abs(v_mantissa_1676_);
lean_dec(v_mantissa_1676_);
v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1702_, v_a_1715_);
if (lean_obj_tag(v___x_1716_) == 1)
{
lean_object* v_val_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1715_);
lean_del_object(v___x_1707_);
v_val_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1744_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_val_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1744_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_nat_abs(v_mantissa_1687_);
lean_dec(v_mantissa_1687_);
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1702_, v_a_1721_);
if (lean_obj_tag(v___x_1722_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1721_);
lean_del_object(v___x_1719_);
lean_del_object(v___x_1713_);
v_val_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1734_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1734_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Expr_letE___override(v_val_1705_, v_val_1711_, v_val_1717_, v_val_1723_, v_b_1700_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v_a_1636_);
lean_ctor_set(v___x_1690_, 0, v___x_1727_);
v___x_1729_ = v___x_1690_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_a_1636_);
v___x_1729_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1729_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec(v___x_1722_);
lean_dec(v_val_1717_);
lean_dec(v_val_1711_);
lean_dec(v_val_1705_);
lean_del_object(v___x_1690_);
lean_dec_ref(v_a_1636_);
v___x_1735_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1736_ = l_Nat_reprFast(v_a_1721_);
v___x_1737_ = lean_string_append(v___x_1735_, v___x_1736_);
lean_dec_ref(v___x_1736_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 18);
lean_ctor_set(v___x_1719_, 0, v___x_1737_);
v___x_1739_ = v___x_1719_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1739_);
v___x_1741_ = v___x_1713_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v___x_1716_);
lean_dec(v_val_1711_);
lean_dec(v_val_1705_);
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_dec_ref(v_a_1636_);
v___x_1745_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1746_ = l_Nat_reprFast(v_a_1715_);
v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
lean_dec_ref(v___x_1746_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 18);
lean_ctor_set(v___x_1713_, 0, v___x_1747_);
v___x_1749_ = v___x_1713_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1749_);
v___x_1751_ = v___x_1707_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_dec(v___x_1710_);
lean_dec(v_val_1705_);
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_dec(v_mantissa_1676_);
lean_dec_ref(v_a_1636_);
v___x_1755_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1756_ = l_Nat_reprFast(v_a_1709_);
v___x_1757_ = lean_string_append(v___x_1755_, v___x_1756_);
lean_dec_ref(v___x_1756_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 18);
lean_ctor_set(v___x_1707_, 0, v___x_1757_);
v___x_1759_ = v___x_1707_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1759_);
v___x_1761_ = v___x_1698_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_dec(v___x_1704_);
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec_ref(v_a_1636_);
v___x_1765_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1766_ = l_Nat_reprFast(v_a_1703_);
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
lean_dec_ref(v___x_1766_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 18);
lean_ctor_set(v___x_1698_, 0, v___x_1767_);
v___x_1769_ = v___x_1698_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1769_);
v___x_1771_ = v___x_1685_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_del_object(v___x_1698_);
lean_dec(v_val_1696_);
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_del_object(v___x_1685_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1650_;
}
}
}
else
{
lean_dec(v___x_1695_);
lean_del_object(v___x_1690_);
lean_dec(v_mantissa_1687_);
lean_del_object(v___x_1685_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1650_;
}
}
}
else
{
lean_del_object(v___x_1690_);
lean_dec(v_exponent_1688_);
lean_dec(v_mantissa_1687_);
lean_del_object(v___x_1685_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1647_;
}
}
}
}
else
{
lean_dec(v_val_1682_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1647_;
}
}
else
{
lean_dec(v___x_1681_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1647_;
}
}
}
else
{
lean_dec(v_exponent_1677_);
lean_dec(v_mantissa_1676_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1644_;
}
}
else
{
lean_dec(v_val_1674_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1644_;
}
}
else
{
lean_dec(v___x_1673_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1644_;
}
}
}
else
{
lean_dec(v_exponent_1669_);
lean_dec(v_mantissa_1668_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1641_;
}
}
else
{
lean_dec(v_val_1666_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1641_;
}
}
else
{
lean_dec(v___x_1665_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1641_;
}
}
}
else
{
lean_dec(v_exponent_1659_);
lean_dec(v_mantissa_1658_);
lean_dec_ref(v_a_1636_);
goto v___jp_1638_;
}
}
else
{
lean_dec(v_val_1656_);
lean_dec_ref(v_a_1636_);
goto v___jp_1638_;
}
}
else
{
lean_dec(v___x_1655_);
lean_dec_ref(v_a_1636_);
goto v___jp_1638_;
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v_a_1636_);
v___x_1777_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
v___jp_1638_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
v___jp_1641_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
v___jp_1644_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
v___jp_1647_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
v___jp_1650_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___boxed(lean_object* v_json_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_json_1779_, v_a_1780_);
lean_dec(v_json_1779_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(lean_object* v_json_1789_, lean_object* v_a_1790_){
_start:
{
if (lean_obj_tag(v_json_1789_) == 5)
{
lean_object* v_kvPairs_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_kvPairs_1801_ = lean_ctor_get(v_json_1789_, 0);
v___x_1802_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2));
v___x_1803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1801_, v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 1)
{
lean_object* v_val_1804_; 
v_val_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v___x_1803_, 1);
if (lean_obj_tag(v_val_1804_) == 2)
{
lean_object* v_n_1805_; lean_object* v_mantissa_1806_; lean_object* v_exponent_1807_; lean_object* v_natZero_1808_; lean_object* v_intZero_1809_; uint8_t v_isNeg_1810_; 
v_n_1805_ = lean_ctor_get(v_val_1804_, 0);
lean_inc_ref(v_n_1805_);
lean_dec_ref_known(v_val_1804_, 1);
v_mantissa_1806_ = lean_ctor_get(v_n_1805_, 0);
lean_inc(v_mantissa_1806_);
v_exponent_1807_ = lean_ctor_get(v_n_1805_, 1);
lean_inc(v_exponent_1807_);
lean_dec_ref(v_n_1805_);
v_natZero_1808_ = lean_unsigned_to_nat(0u);
v_intZero_1809_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1810_ = lean_int_dec_lt(v_mantissa_1806_, v_intZero_1809_);
if (v_isNeg_1810_ == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_eq(v_exponent_1807_, v_natZero_1808_);
lean_dec(v_exponent_1807_);
if (v___x_1811_ == 0)
{
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1792_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3));
v___x_1813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1801_, v___x_1812_);
if (lean_obj_tag(v___x_1813_) == 1)
{
lean_object* v_val_1814_; 
v_val_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v___x_1813_, 1);
if (lean_obj_tag(v_val_1814_) == 2)
{
lean_object* v_n_1815_; lean_object* v_mantissa_1816_; lean_object* v_exponent_1817_; uint8_t v_isNeg_1818_; 
v_n_1815_ = lean_ctor_get(v_val_1814_, 0);
lean_inc_ref(v_n_1815_);
lean_dec_ref_known(v_val_1814_, 1);
v_mantissa_1816_ = lean_ctor_get(v_n_1815_, 0);
lean_inc(v_mantissa_1816_);
v_exponent_1817_ = lean_ctor_get(v_n_1815_, 1);
lean_inc(v_exponent_1817_);
lean_dec_ref(v_n_1815_);
v_isNeg_1818_ = lean_int_dec_lt(v_mantissa_1816_, v_intZero_1809_);
if (v_isNeg_1818_ == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_nat_dec_eq(v_exponent_1817_, v_natZero_1808_);
lean_dec(v_exponent_1817_);
if (v___x_1819_ == 0)
{
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1795_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4));
v___x_1821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1801_, v___x_1820_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1881_; 
v_val_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1881_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1881_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
if (lean_obj_tag(v_val_1822_) == 2)
{
lean_object* v_n_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1880_; 
v_n_1826_ = lean_ctor_get(v_val_1822_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_val_1822_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1828_ = v_val_1822_;
v_isShared_1829_ = v_isSharedCheck_1880_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_n_1826_);
lean_dec(v_val_1822_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1880_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_mantissa_1830_; lean_object* v_exponent_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1879_; 
v_mantissa_1830_ = lean_ctor_get(v_n_1826_, 0);
v_exponent_1831_ = lean_ctor_get(v_n_1826_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_n_1826_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1833_ = v_n_1826_;
v_isShared_1834_ = v_isSharedCheck_1879_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_exponent_1831_);
lean_inc(v_mantissa_1830_);
lean_dec(v_n_1826_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1879_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v_isNeg_1835_; 
v_isNeg_1835_ = lean_int_dec_lt(v_mantissa_1830_, v_intZero_1809_);
if (v_isNeg_1835_ == 0)
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_eq(v_exponent_1831_, v_natZero_1808_);
lean_dec(v_exponent_1831_);
if (v___x_1836_ == 0)
{
lean_del_object(v___x_1833_);
lean_dec(v_mantissa_1830_);
lean_del_object(v___x_1828_);
lean_del_object(v___x_1824_);
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1798_;
}
else
{
lean_object* v_nameMap_1837_; lean_object* v_exprMap_1838_; lean_object* v_a_1839_; lean_object* v___x_1840_; 
v_nameMap_1837_ = lean_ctor_get(v_a_1790_, 1);
v_exprMap_1838_ = lean_ctor_get(v_a_1790_, 3);
v_a_1839_ = lean_nat_abs(v_mantissa_1806_);
lean_dec(v_mantissa_1806_);
v___x_1840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1837_, v_a_1839_);
if (lean_obj_tag(v___x_1840_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1839_);
lean_del_object(v___x_1824_);
v_val_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1869_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_val_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1869_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_nat_abs(v_mantissa_1830_);
lean_dec(v_mantissa_1830_);
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1838_, v_a_1845_);
if (lean_obj_tag(v___x_1846_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1845_);
lean_del_object(v___x_1843_);
lean_del_object(v___x_1828_);
v_val_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v_a_1851_ = lean_nat_abs(v_mantissa_1816_);
lean_dec(v_mantissa_1816_);
v___x_1852_ = l_Lean_Expr_proj___override(v_val_1841_, v_a_1851_, v_val_1847_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v_a_1790_);
lean_ctor_set(v___x_1833_, 0, v___x_1852_);
v___x_1854_ = v___x_1833_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1790_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v___x_1846_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1833_);
lean_dec(v_mantissa_1816_);
lean_dec_ref(v_a_1790_);
v___x_1860_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1861_ = l_Nat_reprFast(v_a_1845_);
v___x_1862_ = lean_string_append(v___x_1860_, v___x_1861_);
lean_dec_ref(v___x_1861_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 18);
lean_ctor_set(v___x_1843_, 0, v___x_1862_);
v___x_1864_ = v___x_1843_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1864_);
v___x_1866_ = v___x_1828_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v___x_1840_);
lean_del_object(v___x_1833_);
lean_dec(v_mantissa_1830_);
lean_dec(v_mantissa_1816_);
lean_dec_ref(v_a_1790_);
v___x_1870_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1871_ = l_Nat_reprFast(v_a_1839_);
v___x_1872_ = lean_string_append(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1871_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 18);
lean_ctor_set(v___x_1828_, 0, v___x_1872_);
v___x_1874_ = v___x_1828_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1874_);
v___x_1876_ = v___x_1824_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_del_object(v___x_1833_);
lean_dec(v_exponent_1831_);
lean_dec(v_mantissa_1830_);
lean_del_object(v___x_1828_);
lean_del_object(v___x_1824_);
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1798_;
}
}
}
}
else
{
lean_del_object(v___x_1824_);
lean_dec(v_val_1822_);
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1798_;
}
}
}
else
{
lean_dec(v___x_1821_);
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1798_;
}
}
}
else
{
lean_dec(v_exponent_1817_);
lean_dec(v_mantissa_1816_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1795_;
}
}
else
{
lean_dec(v_val_1814_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1795_;
}
}
else
{
lean_dec(v___x_1813_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1795_;
}
}
}
else
{
lean_dec(v_exponent_1807_);
lean_dec(v_mantissa_1806_);
lean_dec_ref(v_a_1790_);
goto v___jp_1792_;
}
}
else
{
lean_dec(v_val_1804_);
lean_dec_ref(v_a_1790_);
goto v___jp_1792_;
}
}
else
{
lean_dec(v___x_1803_);
lean_dec_ref(v_a_1790_);
goto v___jp_1792_;
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v_a_1790_);
v___x_1882_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
v___jp_1792_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
v___jp_1795_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
v___jp_1798_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___boxed(lean_object* v_json_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_json_1884_, v_a_1885_);
lean_dec(v_json_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(lean_object* v_json_1891_, lean_object* v_a_1892_){
_start:
{
if (lean_obj_tag(v_json_1891_) == 3)
{
lean_object* v_s_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1919_; 
v_s_1894_ = lean_ctor_get(v_json_1891_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_json_1891_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1896_ = v_json_1891_;
v_isShared_1897_ = v_isSharedCheck_1919_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_s_1894_);
lean_dec(v_json_1891_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1919_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = lean_string_utf8_byte_size(v_s_1894_);
v___x_1900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1900_, 0, v_s_1894_);
lean_ctor_set(v___x_1900_, 1, v___x_1898_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
v___x_1901_ = l_String_Slice_toNat_x3f(v___x_1900_);
lean_dec_ref_known(v___x_1900_, 3);
if (lean_obj_tag(v___x_1901_) == 1)
{
lean_object* v_val_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1914_; 
v_val_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_val_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_val_1902_);
v___x_1907_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1908_ = l_Lean_Expr_lit___override(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v_a_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1909_);
v___x_1911_ = v___x_1896_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v___x_1901_);
lean_dec_ref(v_a_1892_);
v___x_1915_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 1);
lean_ctor_set(v___x_1896_, 0, v___x_1915_);
v___x_1917_ = v___x_1896_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_a_1892_);
lean_dec(v_json_1891_);
v___x_1920_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___boxed(lean_object* v_json_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_json_1922_, v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(lean_object* v_json_1929_, lean_object* v_a_1930_){
_start:
{
if (lean_obj_tag(v_json_1929_) == 3)
{
lean_object* v_s_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1942_; 
v_s_1932_ = lean_ctor_get(v_json_1929_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_json_1929_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1934_ = v_json_1929_;
v_isShared_1935_ = v_isSharedCheck_1942_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_s_1932_);
lean_dec(v_json_1929_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1942_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_s_1932_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = l_Lean_Expr_lit___override(v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v_a_1930_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_a_1930_);
lean_dec(v_json_1929_);
v___x_1943_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1));
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___boxed(lean_object* v_json_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_json_1945_, v_a_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(lean_object* v_json_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_json_1954_) == 5)
{
lean_object* v_kvPairs_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_kvPairs_1963_ = lean_ctor_get(v_json_1954_, 0);
v___x_1964_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2));
v___x_1965_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1963_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 1)
{
lean_object* v_val_1966_; 
v_val_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v___x_1965_, 1);
if (lean_obj_tag(v_val_1966_) == 2)
{
lean_object* v_n_1967_; lean_object* v_mantissa_1968_; lean_object* v_exponent_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2014_; 
v_n_1967_ = lean_ctor_get(v_val_1966_, 0);
lean_inc_ref(v_n_1967_);
lean_dec_ref_known(v_val_1966_, 1);
v_mantissa_1968_ = lean_ctor_get(v_n_1967_, 0);
v_exponent_1969_ = lean_ctor_get(v_n_1967_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_n_1967_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1971_ = v_n_1967_;
v_isShared_1972_ = v_isSharedCheck_2014_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_exponent_1969_);
lean_inc(v_mantissa_1968_);
lean_dec(v_n_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2014_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_natZero_1973_; lean_object* v_intZero_1974_; uint8_t v_isNeg_1975_; 
v_natZero_1973_ = lean_unsigned_to_nat(0u);
v_intZero_1974_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1975_ = lean_int_dec_lt(v_mantissa_1968_, v_intZero_1974_);
if (v_isNeg_1975_ == 0)
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_nat_dec_eq(v_exponent_1969_, v_natZero_1973_);
lean_dec(v_exponent_1969_);
if (v___x_1976_ == 0)
{
lean_del_object(v___x_1971_);
lean_dec(v_mantissa_1968_);
lean_dec_ref(v_a_1955_);
goto v___jp_1957_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3));
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1963_, v___x_1977_);
if (lean_obj_tag(v___x_1978_) == 1)
{
lean_object* v_val_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2013_; 
v_val_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2013_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_val_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2013_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
if (lean_obj_tag(v_val_1979_) == 5)
{
lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2011_; 
v_isSharedCheck_2011_ = !lean_is_exclusive(v_val_1979_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_val_1979_, 0);
lean_dec(v_unused_2012_);
v___x_1984_ = v_val_1979_;
v_isShared_1985_ = v_isSharedCheck_2011_;
goto v_resetjp_1983_;
}
else
{
lean_dec(v_val_1979_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2011_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_exprMap_1986_; lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_exprMap_1986_ = lean_ctor_get(v_a_1955_, 3);
v_a_1987_ = lean_nat_abs(v_mantissa_1968_);
lean_dec(v_mantissa_1968_);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1986_, v_a_1987_);
if (lean_obj_tag(v___x_1988_) == 1)
{
lean_object* v_val_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1987_);
lean_del_object(v___x_1984_);
lean_del_object(v___x_1981_);
v_val_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_val_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1993_ = lean_box(0);
v___x_1994_ = l_Lean_Expr_mdata___override(v___x_1993_, v_val_1989_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v_a_1955_);
lean_ctor_set(v___x_1971_, 0, v___x_1994_);
v___x_1996_ = v___x_1971_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_a_1955_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1996_);
v___x_1998_ = v___x_1991_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v___x_1988_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_a_1955_);
v___x_2002_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2003_ = l_Nat_reprFast(v_a_1987_);
v___x_2004_ = lean_string_append(v___x_2002_, v___x_2003_);
lean_dec_ref(v___x_2003_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 18);
lean_ctor_set(v___x_1984_, 0, v___x_2004_);
v___x_2006_ = v___x_1984_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_2006_);
v___x_2008_ = v___x_1981_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
else
{
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1971_);
lean_dec(v_mantissa_1968_);
lean_dec_ref(v_a_1955_);
goto v___jp_1960_;
}
}
}
else
{
lean_dec(v___x_1978_);
lean_del_object(v___x_1971_);
lean_dec(v_mantissa_1968_);
lean_dec_ref(v_a_1955_);
goto v___jp_1960_;
}
}
}
else
{
lean_del_object(v___x_1971_);
lean_dec(v_exponent_1969_);
lean_dec(v_mantissa_1968_);
lean_dec_ref(v_a_1955_);
goto v___jp_1957_;
}
}
}
else
{
lean_dec(v_val_1966_);
lean_dec_ref(v_a_1955_);
goto v___jp_1957_;
}
}
else
{
lean_dec(v___x_1965_);
lean_dec_ref(v_a_1955_);
goto v___jp_1957_;
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec_ref(v_a_1955_);
v___x_2015_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
v___jp_1957_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___boxed(lean_object* v_json_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_json_2017_, v_a_2018_);
lean_dec(v_json_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = l_List_reverse___redArg(v_x_2025_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___y_2026_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v_head_2034_; 
v_head_2034_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_head_2034_);
if (lean_obj_tag(v_head_2034_) == 2)
{
lean_object* v_n_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2066_; 
v_n_2035_ = lean_ctor_get(v_head_2034_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_head_2034_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2037_ = v_head_2034_;
v_isShared_2038_ = v_isSharedCheck_2066_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_n_2035_);
lean_dec(v_head_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2066_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_tail_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2064_; 
v_tail_2039_ = lean_ctor_get(v_x_2024_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_x_2024_, 0);
lean_dec(v_unused_2065_);
v___x_2041_ = v_x_2024_;
v_isShared_2042_ = v_isSharedCheck_2064_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_tail_2039_);
lean_dec(v_x_2024_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2064_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_mantissa_2043_; lean_object* v_exponent_2044_; lean_object* v_natZero_2045_; lean_object* v_intZero_2046_; uint8_t v_isNeg_2047_; 
v_mantissa_2043_ = lean_ctor_get(v_n_2035_, 0);
lean_inc(v_mantissa_2043_);
v_exponent_2044_ = lean_ctor_get(v_n_2035_, 1);
lean_inc(v_exponent_2044_);
lean_dec_ref(v_n_2035_);
v_natZero_2045_ = lean_unsigned_to_nat(0u);
v_intZero_2046_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2047_ = lean_int_dec_lt(v_mantissa_2043_, v_intZero_2046_);
if (v_isNeg_2047_ == 0)
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_nat_dec_eq(v_exponent_2044_, v_natZero_2045_);
lean_dec(v_exponent_2044_);
if (v___x_2048_ == 0)
{
lean_dec(v_mantissa_2043_);
lean_del_object(v___x_2041_);
lean_dec(v_tail_2039_);
lean_del_object(v___x_2037_);
lean_dec_ref(v___y_2026_);
lean_dec(v_x_2025_);
goto v___jp_2028_;
}
else
{
lean_object* v_nameMap_2049_; lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_nameMap_2049_ = lean_ctor_get(v___y_2026_, 1);
v_a_2050_ = lean_nat_abs(v_mantissa_2043_);
lean_dec(v_mantissa_2043_);
v___x_2051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2051_) == 1)
{
lean_object* v_val_2052_; lean_object* v___x_2054_; 
lean_dec(v_a_2050_);
lean_del_object(v___x_2037_);
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v___x_2051_, 1);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 1, v_x_2025_);
lean_ctor_set(v___x_2041_, 0, v_val_2052_);
v___x_2054_ = v___x_2041_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_val_2052_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_x_2025_);
v___x_2054_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v_x_2024_ = v_tail_2039_;
v_x_2025_ = v___x_2054_;
goto _start;
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_dec(v___x_2051_);
lean_del_object(v___x_2041_);
lean_dec(v_tail_2039_);
lean_dec_ref(v___y_2026_);
lean_dec(v_x_2025_);
v___x_2057_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2058_ = l_Nat_reprFast(v_a_2050_);
v___x_2059_ = lean_string_append(v___x_2057_, v___x_2058_);
lean_dec_ref(v___x_2058_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 18);
lean_ctor_set(v___x_2037_, 0, v___x_2059_);
v___x_2061_ = v___x_2037_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
}
}
else
{
lean_dec(v_exponent_2044_);
lean_dec(v_mantissa_2043_);
lean_del_object(v___x_2041_);
lean_dec(v_tail_2039_);
lean_del_object(v___x_2037_);
lean_dec_ref(v___y_2026_);
lean_dec(v_x_2025_);
goto v___jp_2028_;
}
}
}
}
else
{
lean_dec(v_head_2034_);
lean_dec_ref_known(v_x_2024_, 2);
lean_dec_ref(v___y_2026_);
lean_dec(v_x_2025_);
goto v___jp_2028_;
}
}
v___jp_2028_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1));
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___boxed(lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v_x_2067_, v_x_2068_, v___y_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(lean_object* v_idxs_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_array_to_list(v_idxs_2072_);
v___x_2076_ = lean_box(0);
v___x_2077_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v___x_2075_, v___x_2076_, v_a_2073_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList___boxed(lean_object* v_idxs_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_idxs_2078_, v_a_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 0;
return v___x_2084_;
}
else
{
lean_object* v_key_2085_; lean_object* v_tail_2086_; uint8_t v___x_2087_; 
v_key_2085_ = lean_ctor_get(v_x_2083_, 0);
v_tail_2086_ = lean_ctor_get(v_x_2083_, 2);
v___x_2087_ = lean_name_eq(v_key_2085_, v_a_2082_);
if (v___x_2087_ == 0)
{
v_x_2083_ = v_tail_2086_;
goto _start;
}
else
{
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_2089_, lean_object* v_x_2090_){
_start:
{
uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_res_2091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2089_, v_x_2090_);
lean_dec(v_x_2090_);
lean_dec(v_a_2089_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object* v_m_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_buckets_2095_; lean_object* v___x_2096_; uint64_t v___y_2098_; 
v_buckets_2095_ = lean_ctor_get(v_m_2093_, 1);
v___x_2096_ = lean_array_get_size(v_buckets_2095_);
if (lean_obj_tag(v_a_2094_) == 0)
{
uint64_t v___x_2112_; 
v___x_2112_ = 1723ULL;
v___y_2098_ = v___x_2112_;
goto v___jp_2097_;
}
else
{
uint64_t v_hash_2113_; 
v_hash_2113_ = lean_ctor_get_uint64(v_a_2094_, sizeof(void*)*2);
v___y_2098_ = v_hash_2113_;
goto v___jp_2097_;
}
v___jp_2097_:
{
uint64_t v___x_2099_; uint64_t v___x_2100_; uint64_t v_fold_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2099_ = 32ULL;
v___x_2100_ = lean_uint64_shift_right(v___y_2098_, v___x_2099_);
v_fold_2101_ = lean_uint64_xor(v___y_2098_, v___x_2100_);
v___x_2102_ = 16ULL;
v___x_2103_ = lean_uint64_shift_right(v_fold_2101_, v___x_2102_);
v___x_2104_ = lean_uint64_xor(v_fold_2101_, v___x_2103_);
v___x_2105_ = lean_uint64_to_usize(v___x_2104_);
v___x_2106_ = lean_usize_of_nat(v___x_2096_);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_sub(v___x_2106_, v___x_2107_);
v___x_2109_ = lean_usize_land(v___x_2105_, v___x_2108_);
v___x_2110_ = lean_array_uget_borrowed(v_buckets_2095_, v___x_2109_);
v___x_2111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2094_, v___x_2110_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg___boxed(lean_object* v_m_2114_, lean_object* v_a_2115_){
_start:
{
uint8_t v_res_2116_; lean_object* v_r_2117_; 
v_res_2116_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_m_2114_);
v_r_2117_ = lean_box(v_res_2116_);
return v_r_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
return v_x_2118_;
}
else
{
lean_object* v_key_2120_; lean_object* v_value_2121_; lean_object* v_tail_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2148_; 
v_key_2120_ = lean_ctor_get(v_x_2119_, 0);
v_value_2121_ = lean_ctor_get(v_x_2119_, 1);
v_tail_2122_ = lean_ctor_get(v_x_2119_, 2);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_2119_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2124_ = v_x_2119_;
v_isShared_2125_ = v_isSharedCheck_2148_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_tail_2122_);
lean_inc(v_value_2121_);
lean_inc(v_key_2120_);
lean_dec(v_x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2148_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; uint64_t v___y_2128_; 
v___x_2126_ = lean_array_get_size(v_x_2118_);
if (lean_obj_tag(v_key_2120_) == 0)
{
uint64_t v___x_2146_; 
v___x_2146_ = 1723ULL;
v___y_2128_ = v___x_2146_;
goto v___jp_2127_;
}
else
{
uint64_t v_hash_2147_; 
v_hash_2147_ = lean_ctor_get_uint64(v_key_2120_, sizeof(void*)*2);
v___y_2128_ = v_hash_2147_;
goto v___jp_2127_;
}
v___jp_2127_:
{
uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v_fold_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint64_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2129_ = 32ULL;
v___x_2130_ = lean_uint64_shift_right(v___y_2128_, v___x_2129_);
v_fold_2131_ = lean_uint64_xor(v___y_2128_, v___x_2130_);
v___x_2132_ = 16ULL;
v___x_2133_ = lean_uint64_shift_right(v_fold_2131_, v___x_2132_);
v___x_2134_ = lean_uint64_xor(v_fold_2131_, v___x_2133_);
v___x_2135_ = lean_uint64_to_usize(v___x_2134_);
v___x_2136_ = lean_usize_of_nat(v___x_2126_);
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_sub(v___x_2136_, v___x_2137_);
v___x_2139_ = lean_usize_land(v___x_2135_, v___x_2138_);
v___x_2140_ = lean_array_uget_borrowed(v_x_2118_, v___x_2139_);
lean_inc(v___x_2140_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 2, v___x_2140_);
v___x_2142_ = v___x_2124_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_key_2120_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_value_2121_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_array_uset(v_x_2118_, v___x_2139_, v___x_2142_);
v_x_2118_ = v___x_2143_;
v_x_2119_ = v_tail_2122_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2149_, lean_object* v_source_2150_, lean_object* v_target_2151_){
_start:
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_array_get_size(v_source_2150_);
v___x_2153_ = lean_nat_dec_lt(v_i_2149_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_dec_ref(v_source_2150_);
lean_dec(v_i_2149_);
return v_target_2151_;
}
else
{
lean_object* v_es_2154_; lean_object* v___x_2155_; lean_object* v_source_2156_; lean_object* v_target_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_es_2154_ = lean_array_fget(v_source_2150_, v_i_2149_);
v___x_2155_ = lean_box(0);
v_source_2156_ = lean_array_fset(v_source_2150_, v_i_2149_, v___x_2155_);
v_target_2157_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2151_, v_es_2154_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v_i_2149_, v___x_2158_);
lean_dec(v_i_2149_);
v_i_2149_ = v___x_2159_;
v_source_2150_ = v_source_2156_;
v_target_2151_ = v_target_2157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(lean_object* v_data_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_nbuckets_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = lean_array_get_size(v_data_2161_);
v___x_2163_ = lean_unsigned_to_nat(2u);
v_nbuckets_2164_ = lean_nat_mul(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_mk_array(v_nbuckets_2164_, v___x_2166_);
v___x_2168_ = lean_array_propagate_mark(v_data_2161_, v___x_2167_);
v___x_2169_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v___x_2165_, v_data_2161_, v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(lean_object* v_a_2170_, lean_object* v_b_2171_, lean_object* v_x_2172_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
lean_dec(v_b_2171_);
lean_dec(v_a_2170_);
return v_x_2172_;
}
else
{
lean_object* v_key_2173_; lean_object* v_value_2174_; lean_object* v_tail_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2187_; 
v_key_2173_ = lean_ctor_get(v_x_2172_, 0);
v_value_2174_ = lean_ctor_get(v_x_2172_, 1);
v_tail_2175_ = lean_ctor_get(v_x_2172_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2172_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2177_ = v_x_2172_;
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_tail_2175_);
lean_inc(v_value_2174_);
lean_inc(v_key_2173_);
lean_dec(v_x_2172_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_name_eq(v_key_2173_, v_a_2170_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2170_, v_b_2171_, v_tail_2175_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 2, v___x_2180_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_key_2173_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_value_2174_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v___x_2185_; 
lean_dec(v_value_2174_);
lean_dec(v_key_2173_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_b_2171_);
lean_ctor_set(v___x_2177_, 0, v_a_2170_);
v___x_2185_ = v___x_2177_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2170_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_b_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_tail_2175_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object* v_m_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_){
_start:
{
lean_object* v_size_2191_; lean_object* v_buckets_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2238_; 
v_size_2191_ = lean_ctor_get(v_m_2188_, 0);
v_buckets_2192_ = lean_ctor_get(v_m_2188_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_m_2188_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2194_ = v_m_2188_;
v_isShared_2195_ = v_isSharedCheck_2238_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_buckets_2192_);
lean_inc(v_size_2191_);
lean_dec(v_m_2188_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2238_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; uint64_t v___y_2198_; 
v___x_2196_ = lean_array_get_size(v_buckets_2192_);
if (lean_obj_tag(v_a_2189_) == 0)
{
uint64_t v___x_2236_; 
v___x_2236_ = 1723ULL;
v___y_2198_ = v___x_2236_;
goto v___jp_2197_;
}
else
{
uint64_t v_hash_2237_; 
v_hash_2237_ = lean_ctor_get_uint64(v_a_2189_, sizeof(void*)*2);
v___y_2198_ = v_hash_2237_;
goto v___jp_2197_;
}
v___jp_2197_:
{
uint64_t v___x_2199_; uint64_t v___x_2200_; uint64_t v_fold_2201_; uint64_t v___x_2202_; uint64_t v___x_2203_; uint64_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; size_t v___x_2208_; size_t v___x_2209_; lean_object* v_bkt_2210_; uint8_t v___x_2211_; 
v___x_2199_ = 32ULL;
v___x_2200_ = lean_uint64_shift_right(v___y_2198_, v___x_2199_);
v_fold_2201_ = lean_uint64_xor(v___y_2198_, v___x_2200_);
v___x_2202_ = 16ULL;
v___x_2203_ = lean_uint64_shift_right(v_fold_2201_, v___x_2202_);
v___x_2204_ = lean_uint64_xor(v_fold_2201_, v___x_2203_);
v___x_2205_ = lean_uint64_to_usize(v___x_2204_);
v___x_2206_ = lean_usize_of_nat(v___x_2196_);
v___x_2207_ = ((size_t)1ULL);
v___x_2208_ = lean_usize_sub(v___x_2206_, v___x_2207_);
v___x_2209_ = lean_usize_land(v___x_2205_, v___x_2208_);
v_bkt_2210_ = lean_array_uget_borrowed(v_buckets_2192_, v___x_2209_);
v___x_2211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2189_, v_bkt_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v_size_x27_2213_; lean_object* v___x_2214_; lean_object* v_buckets_x27_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2212_ = lean_unsigned_to_nat(1u);
v_size_x27_2213_ = lean_nat_add(v_size_2191_, v___x_2212_);
lean_dec(v_size_2191_);
lean_inc(v_bkt_2210_);
v___x_2214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2189_);
lean_ctor_set(v___x_2214_, 1, v_b_2190_);
lean_ctor_set(v___x_2214_, 2, v_bkt_2210_);
v_buckets_x27_2215_ = lean_array_uset(v_buckets_2192_, v___x_2209_, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(4u);
v___x_2217_ = lean_nat_mul(v_size_x27_2213_, v___x_2216_);
v___x_2218_ = lean_unsigned_to_nat(3u);
v___x_2219_ = lean_nat_div(v___x_2217_, v___x_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_array_get_size(v_buckets_x27_2215_);
v___x_2221_ = lean_nat_dec_le(v___x_2219_, v___x_2220_);
lean_dec(v___x_2219_);
if (v___x_2221_ == 0)
{
lean_object* v_val_2222_; lean_object* v___x_2224_; 
v_val_2222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_buckets_x27_2215_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v_val_2222_);
lean_ctor_set(v___x_2194_, 0, v_size_x27_2213_);
v___x_2224_ = v___x_2194_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_size_x27_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_val_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
else
{
lean_object* v___x_2227_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v_buckets_x27_2215_);
lean_ctor_set(v___x_2194_, 0, v_size_x27_2213_);
v___x_2227_ = v___x_2194_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_size_x27_2213_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_buckets_x27_2215_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v_buckets_x27_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_inc(v_bkt_2210_);
v___x_2229_ = lean_box(0);
v_buckets_x27_2230_ = lean_array_uset(v_buckets_2192_, v___x_2209_, v___x_2229_);
v___x_2231_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2189_, v_b_2190_, v_bkt_2210_);
v___x_2232_ = lean_array_uset(v_buckets_x27_2230_, v___x_2209_, v___x_2231_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2232_);
v___x_2234_ = v___x_2194_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_size_2191_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(lean_object* v_data_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2244_, v___x_2259_);
if (lean_obj_tag(v___x_2260_) == 1)
{
lean_object* v_val_2261_; 
v_val_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v___x_2260_, 1);
if (lean_obj_tag(v_val_2261_) == 2)
{
lean_object* v_n_2262_; lean_object* v_mantissa_2263_; lean_object* v_exponent_2264_; lean_object* v_natZero_2265_; lean_object* v_intZero_2266_; uint8_t v_isNeg_2267_; 
v_n_2262_ = lean_ctor_get(v_val_2261_, 0);
lean_inc_ref(v_n_2262_);
lean_dec_ref_known(v_val_2261_, 1);
v_mantissa_2263_ = lean_ctor_get(v_n_2262_, 0);
lean_inc(v_mantissa_2263_);
v_exponent_2264_ = lean_ctor_get(v_n_2262_, 1);
lean_inc(v_exponent_2264_);
lean_dec_ref(v_n_2262_);
v_natZero_2265_ = lean_unsigned_to_nat(0u);
v_intZero_2266_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2267_ = lean_int_dec_lt(v_mantissa_2263_, v_intZero_2266_);
if (v_isNeg_2267_ == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_nat_dec_eq(v_exponent_2264_, v_natZero_2265_);
lean_dec(v_exponent_2264_);
if (v___x_2268_ == 0)
{
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2244_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 1)
{
lean_object* v_val_2271_; 
v_val_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2270_, 1);
if (lean_obj_tag(v_val_2271_) == 4)
{
lean_object* v_elems_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_elems_2272_ = lean_ctor_get(v_val_2271_, 0);
lean_inc_ref(v_elems_2272_);
lean_dec_ref_known(v_val_2271_, 1);
v___x_2273_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2244_, v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 1)
{
lean_object* v_val_2275_; 
v_val_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v___x_2274_, 1);
if (lean_obj_tag(v_val_2275_) == 2)
{
lean_object* v_n_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2383_; 
v_n_2276_ = lean_ctor_get(v_val_2275_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_val_2275_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2278_ = v_val_2275_;
v_isShared_2279_ = v_isSharedCheck_2383_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_n_2276_);
lean_dec(v_val_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2383_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_mantissa_2280_; lean_object* v_exponent_2281_; uint8_t v_isNeg_2282_; 
v_mantissa_2280_ = lean_ctor_get(v_n_2276_, 0);
lean_inc(v_mantissa_2280_);
v_exponent_2281_ = lean_ctor_get(v_n_2276_, 1);
lean_inc(v_exponent_2281_);
lean_dec_ref(v_n_2276_);
v_isNeg_2282_ = lean_int_dec_lt(v_mantissa_2280_, v_intZero_2266_);
if (v_isNeg_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_eq(v_exponent_2281_, v_natZero_2265_);
lean_dec(v_exponent_2281_);
if (v___x_2283_ == 0)
{
lean_dec(v_mantissa_2280_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2253_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_2285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2244_, v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 1)
{
lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2382_; 
v_val_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2382_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2382_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
if (lean_obj_tag(v_val_2286_) == 1)
{
uint8_t v_b_2290_; lean_object* v_nameMap_2291_; lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_b_2290_ = lean_ctor_get_uint8(v_val_2286_, 0);
lean_dec_ref_known(v_val_2286_, 0);
v_nameMap_2291_ = lean_ctor_get(v_a_2245_, 1);
v_a_2292_ = lean_nat_abs(v_mantissa_2263_);
lean_dec(v_mantissa_2263_);
v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2291_, v_a_2292_);
if (lean_obj_tag(v___x_2293_) == 1)
{
lean_object* v_val_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2292_);
lean_del_object(v___x_2288_);
lean_del_object(v___x_2278_);
v_val_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2372_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_val_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2372_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2272_, v_a_2245_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2363_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2363_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2363_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_snd_2303_; lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2362_; 
v_snd_2303_ = lean_ctor_get(v_a_2299_, 1);
v_fst_2304_ = lean_ctor_get(v_a_2299_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2299_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2306_ = v_a_2299_;
v_isShared_2307_ = v_isSharedCheck_2362_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2303_);
lean_inc(v_fst_2304_);
lean_dec(v_a_2299_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2362_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_stream_2308_; lean_object* v_nameMap_2309_; lean_object* v_levelMap_2310_; lean_object* v_exprMap_2311_; lean_object* v_recursorRuleMap_2312_; lean_object* v_constMap_2313_; lean_object* v_constOrder_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2361_; 
v_stream_2308_ = lean_ctor_get(v_snd_2303_, 0);
v_nameMap_2309_ = lean_ctor_get(v_snd_2303_, 1);
v_levelMap_2310_ = lean_ctor_get(v_snd_2303_, 2);
v_exprMap_2311_ = lean_ctor_get(v_snd_2303_, 3);
v_recursorRuleMap_2312_ = lean_ctor_get(v_snd_2303_, 4);
v_constMap_2313_ = lean_ctor_get(v_snd_2303_, 5);
v_constOrder_2314_ = lean_ctor_get(v_snd_2303_, 6);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2316_ = v_snd_2303_;
v_isShared_2317_ = v_isSharedCheck_2361_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_constOrder_2314_);
lean_inc(v_constMap_2313_);
lean_inc(v_recursorRuleMap_2312_);
lean_inc(v_exprMap_2311_);
lean_inc(v_levelMap_2310_);
lean_inc(v_nameMap_2309_);
lean_inc(v_stream_2308_);
lean_dec(v_snd_2303_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2361_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_nat_abs(v_mantissa_2280_);
lean_dec(v_mantissa_2280_);
v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2311_, v_a_2318_);
if (lean_obj_tag(v___x_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2318_);
lean_del_object(v___x_2296_);
v_val_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2351_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_val_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2351_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
lean_inc(v_val_2294_);
v___x_2324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2324_, 0, v_val_2294_);
lean_ctor_set(v___x_2324_, 1, v_fst_2304_);
lean_ctor_set(v___x_2324_, 2, v_val_2320_);
v___x_2325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2313_, v_val_2294_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v_b_2290_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set_tag(v___x_2322_, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2326_);
v___x_2328_ = v___x_2322_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2329_ = lean_box(0);
lean_inc(v_val_2294_);
v___x_2330_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2313_, v_val_2294_, v___x_2328_);
v___x_2331_ = lean_array_push(v_constOrder_2314_, v_val_2294_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 6, v___x_2331_);
lean_ctor_set(v___x_2316_, 5, v___x_2330_);
v___x_2333_ = v___x_2316_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_stream_2308_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_nameMap_2309_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_levelMap_2310_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_exprMap_2311_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_recursorRuleMap_2312_);
lean_ctor_set(v_reuseFailAlloc_2340_, 5, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2340_, 6, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2333_);
lean_ctor_set(v___x_2306_, 0, v___x_2329_);
v___x_2335_ = v___x_2306_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2335_);
v___x_2337_ = v___x_2301_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
lean_dec_ref_known(v___x_2324_, 3);
lean_del_object(v___x_2316_);
lean_dec_ref(v_constOrder_2314_);
lean_dec_ref(v_constMap_2313_);
lean_dec_ref(v_recursorRuleMap_2312_);
lean_dec_ref(v_exprMap_2311_);
lean_dec_ref(v_levelMap_2310_);
lean_dec_ref(v_nameMap_2309_);
lean_dec_ref(v_stream_2308_);
lean_del_object(v___x_2306_);
v___x_2342_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2294_, v___x_2325_);
v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
lean_dec_ref(v___x_2343_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set_tag(v___x_2322_, 18);
lean_ctor_set(v___x_2322_, 0, v___x_2344_);
v___x_2346_ = v___x_2322_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 0, v___x_2346_);
v___x_2348_ = v___x_2301_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v___x_2319_);
lean_del_object(v___x_2316_);
lean_dec_ref(v_constOrder_2314_);
lean_dec_ref(v_constMap_2313_);
lean_dec_ref(v_recursorRuleMap_2312_);
lean_dec_ref(v_exprMap_2311_);
lean_dec_ref(v_levelMap_2310_);
lean_dec_ref(v_nameMap_2309_);
lean_dec_ref(v_stream_2308_);
lean_del_object(v___x_2306_);
lean_dec(v_fst_2304_);
lean_dec(v_val_2294_);
v___x_2352_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2353_ = l_Nat_reprFast(v_a_2318_);
v___x_2354_ = lean_string_append(v___x_2352_, v___x_2353_);
lean_dec_ref(v___x_2353_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 18);
lean_ctor_set(v___x_2296_, 0, v___x_2354_);
v___x_2356_ = v___x_2296_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 0, v___x_2356_);
v___x_2358_ = v___x_2301_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2296_);
lean_dec(v_val_2294_);
lean_dec(v_mantissa_2280_);
v_a_2364_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2298_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2298_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_dec(v___x_2293_);
lean_dec(v_mantissa_2280_);
lean_dec_ref(v_elems_2272_);
lean_dec_ref(v_a_2245_);
v___x_2373_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2374_ = l_Nat_reprFast(v_a_2292_);
v___x_2375_ = lean_string_append(v___x_2373_, v___x_2374_);
lean_dec_ref(v___x_2374_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 18);
lean_ctor_set(v___x_2288_, 0, v___x_2375_);
v___x_2377_ = v___x_2288_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2377_);
v___x_2379_ = v___x_2278_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_2288_);
lean_dec(v_val_2286_);
lean_dec(v_mantissa_2280_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2256_;
}
}
}
else
{
lean_dec(v___x_2285_);
lean_dec(v_mantissa_2280_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2256_;
}
}
}
else
{
lean_dec(v_exponent_2281_);
lean_dec(v_mantissa_2280_);
lean_del_object(v___x_2278_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2253_;
}
}
}
else
{
lean_dec(v_val_2275_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2253_;
}
}
else
{
lean_dec(v___x_2274_);
lean_dec_ref(v_elems_2272_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2253_;
}
}
else
{
lean_dec(v_val_2271_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2250_;
}
}
else
{
lean_dec(v___x_2270_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2250_;
}
}
}
else
{
lean_dec(v_exponent_2264_);
lean_dec(v_mantissa_2263_);
lean_dec_ref(v_a_2245_);
goto v___jp_2247_;
}
}
else
{
lean_dec(v_val_2261_);
lean_dec_ref(v_a_2245_);
goto v___jp_2247_;
}
}
else
{
lean_dec(v___x_2260_);
lean_dec_ref(v_a_2245_);
goto v___jp_2247_;
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
v___jp_2250_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
v___jp_2253_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
v___jp_2256_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___boxed(lean_object* v_data_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_data_2384_, v_a_2385_);
lean_dec(v_data_2384_);
return v_res_2387_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_object* v_00_u03b2_2388_, lean_object* v_m_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2389_, v_a_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___boxed(lean_object* v_00_u03b2_2392_, lean_object* v_m_2393_, lean_object* v_a_2394_){
_start:
{
uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_res_2395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(v_00_u03b2_2392_, v_m_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_m_2393_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1(lean_object* v_00_u03b2_2397_, lean_object* v_m_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_m_2398_, v_a_2399_, v_b_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_object* v_00_u03b2_2402_, lean_object* v_a_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2403_, v_x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2406_, lean_object* v_a_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(v_00_u03b2_2406_, v_a_2407_, v_x_2408_);
lean_dec(v_x_2408_);
lean_dec(v_a_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2(lean_object* v_00_u03b2_2411_, lean_object* v_data_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_data_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3(lean_object* v_00_u03b2_2414_, lean_object* v_a_2415_, lean_object* v_b_2416_, lean_object* v_x_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2415_, v_b_2416_, v_x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2419_, lean_object* v_i_2420_, lean_object* v_source_2421_, lean_object* v_target_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v_i_2420_, v_source_2421_, v_target_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2425_, v_x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(lean_object* v_data_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 1)
{
lean_object* v_val_2470_; 
v_val_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2469_, 1);
if (lean_obj_tag(v_val_2470_) == 2)
{
lean_object* v_n_2471_; lean_object* v_mantissa_2472_; lean_object* v_exponent_2473_; lean_object* v_natZero_2474_; lean_object* v_intZero_2475_; uint8_t v_isNeg_2476_; 
v_n_2471_ = lean_ctor_get(v_val_2470_, 0);
lean_inc_ref(v_n_2471_);
lean_dec_ref_known(v_val_2470_, 1);
v_mantissa_2472_ = lean_ctor_get(v_n_2471_, 0);
lean_inc(v_mantissa_2472_);
v_exponent_2473_ = lean_ctor_get(v_n_2471_, 1);
lean_inc(v_exponent_2473_);
lean_dec_ref(v_n_2471_);
v_natZero_2474_ = lean_unsigned_to_nat(0u);
v_intZero_2475_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2476_ = lean_int_dec_lt(v_mantissa_2472_, v_intZero_2475_);
if (v_isNeg_2476_ == 0)
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_eq(v_exponent_2473_, v_natZero_2474_);
lean_dec(v_exponent_2473_);
if (v___x_2477_ == 0)
{
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2444_;
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2478_);
if (lean_obj_tag(v___x_2479_) == 1)
{
lean_object* v_val_2480_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 1);
if (lean_obj_tag(v_val_2480_) == 4)
{
lean_object* v_elems_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_elems_2481_ = lean_ctor_get(v_val_2480_, 0);
lean_inc_ref(v_elems_2481_);
lean_dec_ref_known(v_val_2480_, 1);
v___x_2482_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2482_);
if (lean_obj_tag(v___x_2483_) == 1)
{
lean_object* v_val_2484_; 
v_val_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2483_, 1);
if (lean_obj_tag(v_val_2484_) == 2)
{
lean_object* v_n_2485_; lean_object* v_mantissa_2486_; lean_object* v_exponent_2487_; uint8_t v_isNeg_2488_; 
v_n_2485_ = lean_ctor_get(v_val_2484_, 0);
lean_inc_ref(v_n_2485_);
lean_dec_ref_known(v_val_2484_, 1);
v_mantissa_2486_ = lean_ctor_get(v_n_2485_, 0);
lean_inc(v_mantissa_2486_);
v_exponent_2487_ = lean_ctor_get(v_n_2485_, 1);
lean_inc(v_exponent_2487_);
lean_dec_ref(v_n_2485_);
v_isNeg_2488_ = lean_int_dec_lt(v_mantissa_2486_, v_intZero_2475_);
if (v_isNeg_2488_ == 0)
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_nat_dec_eq(v_exponent_2487_, v_natZero_2474_);
lean_dec(v_exponent_2487_);
if (v___x_2489_ == 0)
{
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2450_;
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 1)
{
lean_object* v_val_2492_; 
v_val_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_val_2492_);
lean_dec_ref_known(v___x_2491_, 1);
if (lean_obj_tag(v_val_2492_) == 2)
{
lean_object* v_n_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2691_; 
v_n_2493_ = lean_ctor_get(v_val_2492_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_val_2492_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2495_ = v_val_2492_;
v_isShared_2496_ = v_isSharedCheck_2691_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_n_2493_);
lean_dec(v_val_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2691_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_mantissa_2497_; lean_object* v_exponent_2498_; uint8_t v_isNeg_2499_; 
v_mantissa_2497_ = lean_ctor_get(v_n_2493_, 0);
lean_inc(v_mantissa_2497_);
v_exponent_2498_ = lean_ctor_get(v_n_2493_, 1);
lean_inc(v_exponent_2498_);
lean_dec_ref(v_n_2493_);
v_isNeg_2499_ = lean_int_dec_lt(v_mantissa_2497_, v_intZero_2475_);
if (v_isNeg_2499_ == 0)
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_nat_dec_eq(v_exponent_2498_, v_natZero_2474_);
lean_dec(v_exponent_2498_);
if (v___x_2500_ == 0)
{
lean_dec(v_mantissa_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2453_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2));
v___x_2502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2501_);
if (lean_obj_tag(v___x_2502_) == 1)
{
lean_object* v_val_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_del_object(v___x_2495_);
v_val_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_val_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2504_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3));
v___x_2505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 1)
{
lean_object* v_val_2506_; 
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v___x_2505_, 1);
if (lean_obj_tag(v_val_2506_) == 3)
{
lean_object* v_s_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_s_2507_ = lean_ctor_get(v_val_2506_, 0);
lean_inc_ref(v_s_2507_);
lean_dec_ref_known(v_val_2506_, 1);
v___x_2508_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2441_, v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 1)
{
lean_object* v_val_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2686_; 
v_val_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2686_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_val_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2686_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
if (lean_obj_tag(v_val_2510_) == 4)
{
lean_object* v_elems_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2685_; 
v_elems_2514_ = lean_ctor_get(v_val_2510_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_val_2510_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2516_ = v_val_2510_;
v_isShared_2517_ = v_isSharedCheck_2685_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_elems_2514_);
lean_dec(v_val_2510_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2685_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_nameMap_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_nameMap_2518_ = lean_ctor_get(v_a_2442_, 1);
v_a_2519_ = lean_nat_abs(v_mantissa_2472_);
lean_dec(v_mantissa_2472_);
v___x_2520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2520_) == 1)
{
lean_object* v_val_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2519_);
lean_del_object(v___x_2516_);
lean_del_object(v___x_2512_);
v_val_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2675_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_val_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2675_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; 
v___x_2525_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2481_, v_a_2442_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2666_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2666_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2666_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_snd_2530_; lean_object* v_fst_2531_; lean_object* v_exprMap_2532_; lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_snd_2530_ = lean_ctor_get(v_a_2526_, 1);
lean_inc(v_snd_2530_);
v_fst_2531_ = lean_ctor_get(v_a_2526_, 0);
lean_inc(v_fst_2531_);
lean_dec(v_a_2526_);
v_exprMap_2532_ = lean_ctor_get(v_snd_2530_, 3);
v_a_2533_ = lean_nat_abs(v_mantissa_2486_);
lean_dec(v_mantissa_2486_);
v___x_2534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2534_) == 1)
{
lean_object* v_val_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_a_2533_);
lean_del_object(v___x_2523_);
v_val_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2656_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_val_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2656_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_nat_abs(v_mantissa_2497_);
lean_dec(v_mantissa_2497_);
v___x_2540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2532_, v_a_2539_);
if (lean_obj_tag(v___x_2540_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_a_2539_);
v_val_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2646_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2646_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___y_2546_; uint8_t v_safety_2547_; lean_object* v___y_2548_; lean_object* v_hints_2608_; lean_object* v___y_2609_; 
switch(lean_obj_tag(v_val_2503_))
{
case 3:
{
lean_object* v_s_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_s_2627_ = lean_ctor_get(v_val_2503_, 0);
lean_inc_ref(v_s_2627_);
lean_dec_ref_known(v_val_2503_, 1);
v___x_2628_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_2629_ = lean_string_dec_eq(v_s_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10));
v___x_2631_ = lean_string_dec_eq(v_s_2627_, v___x_2630_);
lean_dec_ref(v_s_2627_);
if (v___x_2631_ == 0)
{
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_box(1);
v_hints_2608_ = v___x_2632_;
v___y_2609_ = v_snd_2530_;
goto v___jp_2607_;
}
}
else
{
lean_object* v___x_2633_; 
lean_dec_ref(v_s_2627_);
v___x_2633_ = lean_box(0);
v_hints_2608_ = v___x_2633_;
v___y_2609_ = v_snd_2530_;
goto v___jp_2607_;
}
}
case 5:
{
lean_object* v_kvPairs_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_kvPairs_2634_ = lean_ctor_get(v_val_2503_, 0);
lean_inc(v_kvPairs_2634_);
lean_dec_ref_known(v_val_2503_, 1);
v___x_2635_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11));
v___x_2636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2634_, v___x_2635_);
lean_dec(v_kvPairs_2634_);
if (lean_obj_tag(v___x_2636_) == 1)
{
lean_object* v_val_2637_; 
v_val_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v___x_2636_, 1);
if (lean_obj_tag(v_val_2637_) == 2)
{
lean_object* v_n_2638_; lean_object* v_mantissa_2639_; lean_object* v_exponent_2640_; uint8_t v_isNeg_2641_; 
v_n_2638_ = lean_ctor_get(v_val_2637_, 0);
lean_inc_ref(v_n_2638_);
lean_dec_ref_known(v_val_2637_, 1);
v_mantissa_2639_ = lean_ctor_get(v_n_2638_, 0);
lean_inc(v_mantissa_2639_);
v_exponent_2640_ = lean_ctor_get(v_n_2638_, 1);
lean_inc(v_exponent_2640_);
lean_dec_ref(v_n_2638_);
v_isNeg_2641_ = lean_int_dec_lt(v_mantissa_2639_, v_intZero_2475_);
if (v_isNeg_2641_ == 0)
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_eq(v_exponent_2640_, v_natZero_2474_);
lean_dec(v_exponent_2640_);
if (v___x_2642_ == 0)
{
lean_dec(v_mantissa_2639_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
goto v___jp_2465_;
}
else
{
lean_object* v_a_2643_; uint32_t v___x_2644_; lean_object* v___x_2645_; 
v_a_2643_ = lean_nat_abs(v_mantissa_2639_);
lean_dec(v_mantissa_2639_);
v___x_2644_ = lean_uint32_of_nat(v_a_2643_);
lean_dec(v_a_2643_);
v___x_2645_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_2645_, 0, v___x_2644_);
v_hints_2608_ = v___x_2645_;
v___y_2609_ = v_snd_2530_;
goto v___jp_2607_;
}
}
else
{
lean_dec(v_exponent_2640_);
lean_dec(v_mantissa_2639_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
goto v___jp_2465_;
}
}
else
{
lean_dec(v_val_2637_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
goto v___jp_2465_;
}
}
else
{
lean_dec(v___x_2636_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
goto v___jp_2465_;
}
}
default: 
{
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_del_object(v___x_2528_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
goto v___jp_2462_;
}
}
v___jp_2545_:
{
lean_object* v___x_2549_; 
v___x_2549_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2514_, v___y_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2598_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2598_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2598_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_snd_2554_; lean_object* v_fst_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2597_; 
v_snd_2554_ = lean_ctor_get(v_a_2550_, 1);
v_fst_2555_ = lean_ctor_get(v_a_2550_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_a_2550_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2557_ = v_a_2550_;
v_isShared_2558_ = v_isSharedCheck_2597_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_snd_2554_);
lean_inc(v_fst_2555_);
lean_dec(v_a_2550_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2597_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_stream_2559_; lean_object* v_nameMap_2560_; lean_object* v_levelMap_2561_; lean_object* v_exprMap_2562_; lean_object* v_recursorRuleMap_2563_; lean_object* v_constMap_2564_; lean_object* v_constOrder_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2596_; 
v_stream_2559_ = lean_ctor_get(v_snd_2554_, 0);
v_nameMap_2560_ = lean_ctor_get(v_snd_2554_, 1);
v_levelMap_2561_ = lean_ctor_get(v_snd_2554_, 2);
v_exprMap_2562_ = lean_ctor_get(v_snd_2554_, 3);
v_recursorRuleMap_2563_ = lean_ctor_get(v_snd_2554_, 4);
v_constMap_2564_ = lean_ctor_get(v_snd_2554_, 5);
v_constOrder_2565_ = lean_ctor_get(v_snd_2554_, 6);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_snd_2554_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2567_ = v_snd_2554_;
v_isShared_2568_ = v_isSharedCheck_2596_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_constOrder_2565_);
lean_inc(v_constMap_2564_);
lean_inc(v_recursorRuleMap_2563_);
lean_inc(v_exprMap_2562_);
lean_inc(v_levelMap_2561_);
lean_inc(v_nameMap_2560_);
lean_inc(v_stream_2559_);
lean_dec(v_snd_2554_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2596_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2564_, v_val_2521_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
lean_inc(v_val_2521_);
v___x_2570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2570_, 0, v_val_2521_);
lean_ctor_set(v___x_2570_, 1, v_fst_2531_);
lean_ctor_set(v___x_2570_, 2, v_val_2535_);
v___x_2571_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v_val_2541_);
lean_ctor_set(v___x_2571_, 2, v___y_2546_);
lean_ctor_set(v___x_2571_, 3, v_fst_2555_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*4, v_safety_2547_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2571_);
v___x_2573_ = v___x_2543_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2574_ = lean_box(0);
lean_inc(v_val_2521_);
v___x_2575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2564_, v_val_2521_, v___x_2573_);
v___x_2576_ = lean_array_push(v_constOrder_2565_, v_val_2521_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 6, v___x_2576_);
lean_ctor_set(v___x_2567_, 5, v___x_2575_);
v___x_2578_ = v___x_2567_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_stream_2559_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nameMap_2560_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_levelMap_2561_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_exprMap_2562_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_recursorRuleMap_2563_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v___x_2578_);
lean_ctor_set(v___x_2557_, 0, v___x_2574_);
v___x_2580_ = v___x_2557_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2580_);
v___x_2582_ = v___x_2552_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_del_object(v___x_2567_);
lean_dec_ref(v_constOrder_2565_);
lean_dec_ref(v_constMap_2564_);
lean_dec_ref(v_recursorRuleMap_2563_);
lean_dec_ref(v_exprMap_2562_);
lean_dec_ref(v_levelMap_2561_);
lean_dec_ref(v_nameMap_2560_);
lean_dec_ref(v_stream_2559_);
lean_del_object(v___x_2557_);
lean_dec(v_fst_2555_);
lean_dec(v___y_2546_);
lean_dec(v_val_2541_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
v___x_2587_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2521_, v___x_2569_);
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
lean_dec_ref(v___x_2588_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 18);
lean_ctor_set(v___x_2543_, 0, v___x_2589_);
v___x_2591_ = v___x_2543_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2593_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 1);
lean_ctor_set(v___x_2552_, 0, v___x_2591_);
v___x_2593_ = v___x_2552_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v___y_2546_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_val_2521_);
v_a_2599_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2549_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2549_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
v___jp_2607_:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5));
v___x_2611_ = lean_string_dec_eq(v_s_2507_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6));
v___x_2613_ = lean_string_dec_eq(v_s_2507_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7));
v___x_2615_ = lean_string_dec_eq(v_s_2507_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec_ref(v___y_2609_);
lean_dec(v_hints_2608_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
v___x_2616_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8));
v___x_2617_ = lean_string_append(v___x_2616_, v_s_2507_);
lean_dec_ref(v_s_2507_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set_tag(v___x_2537_, 18);
lean_ctor_set(v___x_2537_, 0, v___x_2617_);
v___x_2619_ = v___x_2537_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v___x_2619_);
v___x_2621_ = v___x_2528_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
else
{
uint8_t v___x_2624_; 
lean_del_object(v___x_2537_);
lean_del_object(v___x_2528_);
lean_dec_ref(v_s_2507_);
v___x_2624_ = 2;
v___y_2546_ = v_hints_2608_;
v_safety_2547_ = v___x_2624_;
v___y_2548_ = v___y_2609_;
goto v___jp_2545_;
}
}
else
{
uint8_t v___x_2625_; 
lean_del_object(v___x_2537_);
lean_del_object(v___x_2528_);
lean_dec_ref(v_s_2507_);
v___x_2625_ = 1;
v___y_2546_ = v_hints_2608_;
v_safety_2547_ = v___x_2625_;
v___y_2548_ = v___y_2609_;
goto v___jp_2545_;
}
}
else
{
uint8_t v___x_2626_; 
lean_del_object(v___x_2537_);
lean_del_object(v___x_2528_);
lean_dec_ref(v_s_2507_);
v___x_2626_ = 0;
v___y_2546_ = v_hints_2608_;
v_safety_2547_ = v___x_2626_;
v___y_2548_ = v___y_2609_;
goto v___jp_2545_;
}
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_dec(v___x_2540_);
lean_dec(v_val_2535_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
v___x_2647_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2648_ = l_Nat_reprFast(v_a_2539_);
v___x_2649_ = lean_string_append(v___x_2647_, v___x_2648_);
lean_dec_ref(v___x_2648_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set_tag(v___x_2537_, 18);
lean_ctor_set(v___x_2537_, 0, v___x_2649_);
v___x_2651_ = v___x_2537_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v___x_2651_);
v___x_2653_ = v___x_2528_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_dec(v___x_2534_);
lean_dec(v_fst_2531_);
lean_dec(v_snd_2530_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
v___x_2657_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2658_ = l_Nat_reprFast(v_a_2533_);
v___x_2659_ = lean_string_append(v___x_2657_, v___x_2658_);
lean_dec_ref(v___x_2658_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set_tag(v___x_2523_, 18);
lean_ctor_set(v___x_2523_, 0, v___x_2659_);
v___x_2661_ = v___x_2523_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v___x_2661_);
v___x_2663_ = v___x_2528_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_del_object(v___x_2523_);
lean_dec(v_val_2521_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
v_a_2667_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2525_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2525_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
lean_dec(v___x_2520_);
lean_dec_ref(v_elems_2514_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec_ref(v_a_2442_);
v___x_2676_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2677_ = l_Nat_reprFast(v_a_2519_);
v___x_2678_ = lean_string_append(v___x_2676_, v___x_2677_);
lean_dec_ref(v___x_2677_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 18);
lean_ctor_set(v___x_2516_, 0, v___x_2678_);
v___x_2680_ = v___x_2516_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2680_);
v___x_2682_ = v___x_2512_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_del_object(v___x_2512_);
lean_dec(v_val_2510_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2459_;
}
}
}
else
{
lean_dec(v___x_2509_);
lean_dec_ref(v_s_2507_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2459_;
}
}
else
{
lean_dec(v_val_2506_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2456_;
}
}
else
{
lean_dec(v___x_2505_);
lean_dec(v_val_2503_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2456_;
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec(v___x_2502_);
lean_dec(v_mantissa_2497_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
v___x_2687_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2687_);
v___x_2689_ = v___x_2495_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_dec(v_exponent_2498_);
lean_dec(v_mantissa_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2453_;
}
}
}
else
{
lean_dec(v_val_2492_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2453_;
}
}
else
{
lean_dec(v___x_2491_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2453_;
}
}
}
else
{
lean_dec(v_exponent_2487_);
lean_dec(v_mantissa_2486_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2450_;
}
}
else
{
lean_dec(v_val_2484_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2450_;
}
}
else
{
lean_dec(v___x_2483_);
lean_dec_ref(v_elems_2481_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2450_;
}
}
else
{
lean_dec(v_val_2480_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2447_;
}
}
else
{
lean_dec(v___x_2479_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2447_;
}
}
}
else
{
lean_dec(v_exponent_2473_);
lean_dec(v_mantissa_2472_);
lean_dec_ref(v_a_2442_);
goto v___jp_2444_;
}
}
else
{
lean_dec(v_val_2470_);
lean_dec_ref(v_a_2442_);
goto v___jp_2444_;
}
}
else
{
lean_dec(v___x_2469_);
lean_dec_ref(v_a_2442_);
goto v___jp_2444_;
}
v___jp_2444_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
v___jp_2447_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
v___jp_2450_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
v___jp_2453_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
v___jp_2456_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
v___jp_2459_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
v___jp_2462_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___boxed(lean_object* v_data_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_data_2692_, v_a_2693_);
lean_dec(v_data_2692_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(lean_object* v_data_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2699_, v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 1)
{
lean_object* v_val_2719_; 
v_val_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___x_2718_, 1);
if (lean_obj_tag(v_val_2719_) == 2)
{
lean_object* v_n_2720_; lean_object* v_mantissa_2721_; lean_object* v_exponent_2722_; lean_object* v_natZero_2723_; lean_object* v_intZero_2724_; uint8_t v_isNeg_2725_; 
v_n_2720_ = lean_ctor_get(v_val_2719_, 0);
lean_inc_ref(v_n_2720_);
lean_dec_ref_known(v_val_2719_, 1);
v_mantissa_2721_ = lean_ctor_get(v_n_2720_, 0);
lean_inc(v_mantissa_2721_);
v_exponent_2722_ = lean_ctor_get(v_n_2720_, 1);
lean_inc(v_exponent_2722_);
lean_dec_ref(v_n_2720_);
v_natZero_2723_ = lean_unsigned_to_nat(0u);
v_intZero_2724_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2725_ = lean_int_dec_lt(v_mantissa_2721_, v_intZero_2724_);
if (v_isNeg_2725_ == 0)
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_nat_dec_eq(v_exponent_2722_, v_natZero_2723_);
lean_dec(v_exponent_2722_);
if (v___x_2726_ == 0)
{
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2702_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2728_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2699_, v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 1)
{
lean_object* v_val_2729_; 
v_val_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_val_2729_);
lean_dec_ref_known(v___x_2728_, 1);
if (lean_obj_tag(v_val_2729_) == 4)
{
lean_object* v_elems_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_elems_2730_ = lean_ctor_get(v_val_2729_, 0);
lean_inc_ref(v_elems_2730_);
lean_dec_ref_known(v_val_2729_, 1);
v___x_2731_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2699_, v___x_2731_);
if (lean_obj_tag(v___x_2732_) == 1)
{
lean_object* v_val_2733_; 
v_val_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v___x_2732_, 1);
if (lean_obj_tag(v_val_2733_) == 2)
{
lean_object* v_n_2734_; lean_object* v_mantissa_2735_; lean_object* v_exponent_2736_; uint8_t v_isNeg_2737_; 
v_n_2734_ = lean_ctor_get(v_val_2733_, 0);
lean_inc_ref(v_n_2734_);
lean_dec_ref_known(v_val_2733_, 1);
v_mantissa_2735_ = lean_ctor_get(v_n_2734_, 0);
lean_inc(v_mantissa_2735_);
v_exponent_2736_ = lean_ctor_get(v_n_2734_, 1);
lean_inc(v_exponent_2736_);
lean_dec_ref(v_n_2734_);
v_isNeg_2737_ = lean_int_dec_lt(v_mantissa_2735_, v_intZero_2724_);
if (v_isNeg_2737_ == 0)
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_nat_dec_eq(v_exponent_2736_, v_natZero_2723_);
lean_dec(v_exponent_2736_);
if (v___x_2738_ == 0)
{
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2708_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2699_, v___x_2739_);
if (lean_obj_tag(v___x_2740_) == 1)
{
lean_object* v_val_2741_; 
v_val_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_val_2741_);
lean_dec_ref_known(v___x_2740_, 1);
if (lean_obj_tag(v_val_2741_) == 2)
{
lean_object* v_n_2742_; lean_object* v_mantissa_2743_; lean_object* v_exponent_2744_; uint8_t v_isNeg_2745_; 
v_n_2742_ = lean_ctor_get(v_val_2741_, 0);
lean_inc_ref(v_n_2742_);
lean_dec_ref_known(v_val_2741_, 1);
v_mantissa_2743_ = lean_ctor_get(v_n_2742_, 0);
lean_inc(v_mantissa_2743_);
v_exponent_2744_ = lean_ctor_get(v_n_2742_, 1);
lean_inc(v_exponent_2744_);
lean_dec_ref(v_n_2742_);
v_isNeg_2745_ = lean_int_dec_lt(v_mantissa_2743_, v_intZero_2724_);
if (v_isNeg_2745_ == 0)
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_nat_dec_eq(v_exponent_2744_, v_natZero_2723_);
lean_dec(v_exponent_2744_);
if (v___x_2746_ == 0)
{
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2711_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2699_, v___x_2747_);
if (lean_obj_tag(v___x_2748_) == 1)
{
lean_object* v_val_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2882_; 
v_val_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2882_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_val_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2882_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
if (lean_obj_tag(v_val_2749_) == 4)
{
lean_object* v_elems_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2881_; 
v_elems_2753_ = lean_ctor_get(v_val_2749_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_val_2749_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2755_ = v_val_2749_;
v_isShared_2756_ = v_isSharedCheck_2881_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_elems_2753_);
lean_dec(v_val_2749_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2881_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_nameMap_2757_; lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_nameMap_2757_ = lean_ctor_get(v_a_2700_, 1);
v_a_2758_ = lean_nat_abs(v_mantissa_2721_);
lean_dec(v_mantissa_2721_);
v___x_2759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2759_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2758_);
lean_del_object(v___x_2755_);
lean_del_object(v___x_2751_);
v_val_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2871_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_val_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2871_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; 
v___x_2764_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2730_, v_a_2700_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2862_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2862_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2862_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v_snd_2769_; lean_object* v_fst_2770_; lean_object* v_exprMap_2771_; lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_snd_2769_ = lean_ctor_get(v_a_2765_, 1);
lean_inc(v_snd_2769_);
v_fst_2770_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_fst_2770_);
lean_dec(v_a_2765_);
v_exprMap_2771_ = lean_ctor_get(v_snd_2769_, 3);
v_a_2772_ = lean_nat_abs(v_mantissa_2735_);
lean_dec(v_mantissa_2735_);
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2773_) == 1)
{
lean_object* v_val_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_a_2772_);
lean_del_object(v___x_2762_);
v_val_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2852_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_val_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2852_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_nat_abs(v_mantissa_2743_);
lean_dec(v_mantissa_2743_);
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2771_, v_a_2778_);
if (lean_obj_tag(v___x_2779_) == 1)
{
lean_object* v_val_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2778_);
lean_del_object(v___x_2776_);
lean_del_object(v___x_2767_);
v_val_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2842_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_val_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2842_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2753_, v_snd_2769_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2833_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2833_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2833_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_snd_2789_; lean_object* v_fst_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2832_; 
v_snd_2789_ = lean_ctor_get(v_a_2785_, 1);
v_fst_2790_ = lean_ctor_get(v_a_2785_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_a_2785_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2792_ = v_a_2785_;
v_isShared_2793_ = v_isSharedCheck_2832_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_snd_2789_);
lean_inc(v_fst_2790_);
lean_dec(v_a_2785_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2832_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_stream_2794_; lean_object* v_nameMap_2795_; lean_object* v_levelMap_2796_; lean_object* v_exprMap_2797_; lean_object* v_recursorRuleMap_2798_; lean_object* v_constMap_2799_; lean_object* v_constOrder_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2831_; 
v_stream_2794_ = lean_ctor_get(v_snd_2789_, 0);
v_nameMap_2795_ = lean_ctor_get(v_snd_2789_, 1);
v_levelMap_2796_ = lean_ctor_get(v_snd_2789_, 2);
v_exprMap_2797_ = lean_ctor_get(v_snd_2789_, 3);
v_recursorRuleMap_2798_ = lean_ctor_get(v_snd_2789_, 4);
v_constMap_2799_ = lean_ctor_get(v_snd_2789_, 5);
v_constOrder_2800_ = lean_ctor_get(v_snd_2789_, 6);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_snd_2789_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2802_ = v_snd_2789_;
v_isShared_2803_ = v_isSharedCheck_2831_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_constOrder_2800_);
lean_inc(v_constMap_2799_);
lean_inc(v_recursorRuleMap_2798_);
lean_inc(v_exprMap_2797_);
lean_inc(v_levelMap_2796_);
lean_inc(v_nameMap_2795_);
lean_inc(v_stream_2794_);
lean_dec(v_snd_2789_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2831_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
uint8_t v___x_2804_; 
v___x_2804_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2799_, v_val_2760_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_inc(v_val_2760_);
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v_val_2760_);
lean_ctor_set(v___x_2805_, 1, v_fst_2770_);
lean_ctor_set(v___x_2805_, 2, v_val_2774_);
v___x_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v_val_2780_);
lean_ctor_set(v___x_2806_, 2, v_fst_2790_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 2);
lean_ctor_set(v___x_2782_, 0, v___x_2806_);
v___x_2808_ = v___x_2782_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2809_ = lean_box(0);
lean_inc(v_val_2760_);
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2799_, v_val_2760_, v___x_2808_);
v___x_2811_ = lean_array_push(v_constOrder_2800_, v_val_2760_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 6, v___x_2811_);
lean_ctor_set(v___x_2802_, 5, v___x_2810_);
v___x_2813_ = v___x_2802_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_stream_2794_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_nameMap_2795_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_levelMap_2796_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v_exprMap_2797_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v_recursorRuleMap_2798_);
lean_ctor_set(v_reuseFailAlloc_2820_, 5, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2820_, 6, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2813_);
lean_ctor_set(v___x_2792_, 0, v___x_2809_);
v___x_2815_ = v___x_2792_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2817_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2815_);
v___x_2817_ = v___x_2787_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
lean_del_object(v___x_2802_);
lean_dec_ref(v_constOrder_2800_);
lean_dec_ref(v_constMap_2799_);
lean_dec_ref(v_recursorRuleMap_2798_);
lean_dec_ref(v_exprMap_2797_);
lean_dec_ref(v_levelMap_2796_);
lean_dec_ref(v_nameMap_2795_);
lean_dec_ref(v_stream_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_dec(v_val_2780_);
lean_dec(v_val_2774_);
lean_dec(v_fst_2770_);
v___x_2822_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2760_, v___x_2804_);
v___x_2824_ = lean_string_append(v___x_2822_, v___x_2823_);
lean_dec_ref(v___x_2823_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 18);
lean_ctor_set(v___x_2782_, 0, v___x_2824_);
v___x_2826_ = v___x_2782_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 1);
lean_ctor_set(v___x_2787_, 0, v___x_2826_);
v___x_2828_ = v___x_2787_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_del_object(v___x_2782_);
lean_dec(v_val_2780_);
lean_dec(v_val_2774_);
lean_dec(v_fst_2770_);
lean_dec(v_val_2760_);
v_a_2834_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2784_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2784_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_dec(v___x_2779_);
lean_dec(v_val_2774_);
lean_dec(v_fst_2770_);
lean_dec(v_snd_2769_);
lean_dec(v_val_2760_);
lean_dec_ref(v_elems_2753_);
v___x_2843_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2844_ = l_Nat_reprFast(v_a_2778_);
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
lean_dec_ref(v___x_2844_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 18);
lean_ctor_set(v___x_2776_, 0, v___x_2845_);
v___x_2847_ = v___x_2776_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2849_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 1);
lean_ctor_set(v___x_2767_, 0, v___x_2847_);
v___x_2849_ = v___x_2767_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
lean_dec(v___x_2773_);
lean_dec(v_fst_2770_);
lean_dec(v_snd_2769_);
lean_dec(v_val_2760_);
lean_dec_ref(v_elems_2753_);
lean_dec(v_mantissa_2743_);
v___x_2853_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2854_ = l_Nat_reprFast(v_a_2772_);
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
lean_dec_ref(v___x_2854_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 18);
lean_ctor_set(v___x_2762_, 0, v___x_2855_);
v___x_2857_ = v___x_2762_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2859_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 1);
lean_ctor_set(v___x_2767_, 0, v___x_2857_);
v___x_2859_ = v___x_2767_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2762_);
lean_dec(v_val_2760_);
lean_dec_ref(v_elems_2753_);
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
v_a_2863_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2764_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2764_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
lean_dec(v___x_2759_);
lean_dec_ref(v_elems_2753_);
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec_ref(v_a_2700_);
v___x_2872_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2873_ = l_Nat_reprFast(v_a_2758_);
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
lean_dec_ref(v___x_2873_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 18);
lean_ctor_set(v___x_2755_, 0, v___x_2874_);
v___x_2876_ = v___x_2755_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2876_);
v___x_2878_ = v___x_2751_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_del_object(v___x_2751_);
lean_dec(v_val_2749_);
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2714_;
}
}
}
else
{
lean_dec(v___x_2748_);
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2714_;
}
}
}
else
{
lean_dec(v_exponent_2744_);
lean_dec(v_mantissa_2743_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2711_;
}
}
else
{
lean_dec(v_val_2741_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2711_;
}
}
else
{
lean_dec(v___x_2740_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2711_;
}
}
}
else
{
lean_dec(v_exponent_2736_);
lean_dec(v_mantissa_2735_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_val_2733_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v___x_2732_);
lean_dec_ref(v_elems_2730_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2708_;
}
}
else
{
lean_dec(v_val_2729_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2705_;
}
}
else
{
lean_dec(v___x_2728_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2705_;
}
}
}
else
{
lean_dec(v_exponent_2722_);
lean_dec(v_mantissa_2721_);
lean_dec_ref(v_a_2700_);
goto v___jp_2702_;
}
}
else
{
lean_dec(v_val_2719_);
lean_dec_ref(v_a_2700_);
goto v___jp_2702_;
}
}
else
{
lean_dec(v___x_2718_);
lean_dec_ref(v_a_2700_);
goto v___jp_2702_;
}
v___jp_2702_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
v___jp_2705_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
v___jp_2708_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
v___jp_2711_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
return v___x_2713_;
}
v___jp_2714_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___boxed(lean_object* v_data_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_data_2883_, v_a_2884_);
lean_dec(v_data_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(lean_object* v_data_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_2908_);
if (lean_obj_tag(v___x_2909_) == 1)
{
lean_object* v_val_2910_; 
v_val_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v___x_2909_, 1);
if (lean_obj_tag(v_val_2910_) == 2)
{
lean_object* v_n_2911_; lean_object* v_mantissa_2912_; lean_object* v_exponent_2913_; lean_object* v_natZero_2914_; lean_object* v_intZero_2915_; uint8_t v_isNeg_2916_; 
v_n_2911_ = lean_ctor_get(v_val_2910_, 0);
lean_inc_ref(v_n_2911_);
lean_dec_ref_known(v_val_2910_, 1);
v_mantissa_2912_ = lean_ctor_get(v_n_2911_, 0);
lean_inc(v_mantissa_2912_);
v_exponent_2913_ = lean_ctor_get(v_n_2911_, 1);
lean_inc(v_exponent_2913_);
lean_dec_ref(v_n_2911_);
v_natZero_2914_ = lean_unsigned_to_nat(0u);
v_intZero_2915_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2916_ = lean_int_dec_lt(v_mantissa_2912_, v_intZero_2915_);
if (v_isNeg_2916_ == 0)
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_nat_dec_eq(v_exponent_2913_, v_natZero_2914_);
lean_dec(v_exponent_2913_);
if (v___x_2917_ == 0)
{
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2905_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2919_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_2918_);
if (lean_obj_tag(v___x_2919_) == 1)
{
lean_object* v_val_2920_; 
v_val_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_val_2920_);
lean_dec_ref_known(v___x_2919_, 1);
if (lean_obj_tag(v_val_2920_) == 4)
{
lean_object* v_elems_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_elems_2921_ = lean_ctor_get(v_val_2920_, 0);
lean_inc_ref(v_elems_2921_);
lean_dec_ref_known(v_val_2920_, 1);
v___x_2922_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2923_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 1)
{
lean_object* v_val_2924_; 
v_val_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v___x_2923_, 1);
if (lean_obj_tag(v_val_2924_) == 2)
{
lean_object* v_n_2925_; lean_object* v_mantissa_2926_; lean_object* v_exponent_2927_; uint8_t v_isNeg_2928_; 
v_n_2925_ = lean_ctor_get(v_val_2924_, 0);
lean_inc_ref(v_n_2925_);
lean_dec_ref_known(v_val_2924_, 1);
v_mantissa_2926_ = lean_ctor_get(v_n_2925_, 0);
lean_inc(v_mantissa_2926_);
v_exponent_2927_ = lean_ctor_get(v_n_2925_, 1);
lean_inc(v_exponent_2927_);
lean_dec_ref(v_n_2925_);
v_isNeg_2928_ = lean_int_dec_lt(v_mantissa_2926_, v_intZero_2915_);
if (v_isNeg_2928_ == 0)
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_nat_dec_eq(v_exponent_2927_, v_natZero_2914_);
lean_dec(v_exponent_2927_);
if (v___x_2929_ == 0)
{
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2899_;
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 1)
{
lean_object* v_val_2932_; 
v_val_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_val_2932_);
lean_dec_ref_known(v___x_2931_, 1);
if (lean_obj_tag(v_val_2932_) == 2)
{
lean_object* v_n_2933_; lean_object* v_mantissa_2934_; lean_object* v_exponent_2935_; uint8_t v_isNeg_2936_; 
v_n_2933_ = lean_ctor_get(v_val_2932_, 0);
lean_inc_ref(v_n_2933_);
lean_dec_ref_known(v_val_2932_, 1);
v_mantissa_2934_ = lean_ctor_get(v_n_2933_, 0);
lean_inc(v_mantissa_2934_);
v_exponent_2935_ = lean_ctor_get(v_n_2933_, 1);
lean_inc(v_exponent_2935_);
lean_dec_ref(v_n_2933_);
v_isNeg_2936_ = lean_int_dec_lt(v_mantissa_2934_, v_intZero_2915_);
if (v_isNeg_2936_ == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = lean_nat_dec_eq(v_exponent_2935_, v_natZero_2914_);
lean_dec(v_exponent_2935_);
if (v___x_2937_ == 0)
{
lean_dec(v_mantissa_2934_);
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2896_;
}
else
{
lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v_a_2940_; uint8_t v_b_2942_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_2938_ = lean_nat_abs(v_mantissa_2912_);
lean_dec(v_mantissa_2912_);
v_a_2939_ = lean_nat_abs(v_mantissa_2926_);
lean_dec(v_mantissa_2926_);
v_a_2940_ = lean_nat_abs(v_mantissa_2934_);
lean_dec(v_mantissa_2934_);
v___x_3076_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
v_b_2942_ = v_isNeg_2936_;
goto v___jp_2941_;
}
else
{
lean_object* v_val_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3087_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_val_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
if (lean_obj_tag(v_val_3078_) == 1)
{
uint8_t v_b_3082_; 
lean_del_object(v___x_3080_);
v_b_3082_ = lean_ctor_get_uint8(v_val_3078_, 0);
lean_dec_ref_known(v_val_3078_, 0);
v_b_2942_ = v_b_3082_;
goto v___jp_2941_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec(v_val_3078_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_elems_2921_);
lean_dec_ref(v_a_2891_);
v___x_3083_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3083_);
v___x_3085_ = v___x_3080_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
v___jp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2890_, v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 1)
{
lean_object* v_val_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3075_; 
v_val_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3075_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_val_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3075_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_val_2945_) == 4)
{
lean_object* v_elems_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3074_; 
v_elems_2949_ = lean_ctor_get(v_val_2945_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_val_2945_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_2951_ = v_val_2945_;
v_isShared_2952_ = v_isSharedCheck_3074_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_elems_2949_);
lean_dec(v_val_2945_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3074_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_nameMap_2953_; lean_object* v___x_2954_; 
v_nameMap_2953_ = lean_ctor_get(v_a_2891_, 1);
v___x_2954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2953_, v_a_2938_);
if (lean_obj_tag(v___x_2954_) == 1)
{
lean_object* v_val_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3064_; 
lean_del_object(v___x_2951_);
lean_del_object(v___x_2947_);
lean_dec(v_a_2938_);
v_val_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_3064_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_val_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3064_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; 
v___x_2959_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2921_, v_a_2891_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3055_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_3055_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3055_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_snd_2964_; lean_object* v_fst_2965_; lean_object* v_exprMap_2966_; lean_object* v___x_2967_; 
v_snd_2964_ = lean_ctor_get(v_a_2960_, 1);
lean_inc(v_snd_2964_);
v_fst_2965_ = lean_ctor_get(v_a_2960_, 0);
lean_inc(v_fst_2965_);
lean_dec(v_a_2960_);
v_exprMap_2966_ = lean_ctor_get(v_snd_2964_, 3);
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2966_, v_a_2939_);
if (lean_obj_tag(v___x_2967_) == 1)
{
lean_object* v_val_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_2957_);
lean_dec(v_a_2939_);
v_val_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_3045_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_val_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3045_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2966_, v_a_2940_);
if (lean_obj_tag(v___x_2972_) == 1)
{
lean_object* v_val_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3035_; 
lean_del_object(v___x_2970_);
lean_del_object(v___x_2962_);
lean_dec(v_a_2940_);
v_val_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_3035_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_val_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3035_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2949_, v_snd_2964_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3026_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_3026_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3026_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v_snd_2982_; lean_object* v_fst_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3025_; 
v_snd_2982_ = lean_ctor_get(v_a_2978_, 1);
v_fst_2983_ = lean_ctor_get(v_a_2978_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_2978_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2985_ = v_a_2978_;
v_isShared_2986_ = v_isSharedCheck_3025_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_snd_2982_);
lean_inc(v_fst_2983_);
lean_dec(v_a_2978_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3025_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v_stream_2987_; lean_object* v_nameMap_2988_; lean_object* v_levelMap_2989_; lean_object* v_exprMap_2990_; lean_object* v_recursorRuleMap_2991_; lean_object* v_constMap_2992_; lean_object* v_constOrder_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3024_; 
v_stream_2987_ = lean_ctor_get(v_snd_2982_, 0);
v_nameMap_2988_ = lean_ctor_get(v_snd_2982_, 1);
v_levelMap_2989_ = lean_ctor_get(v_snd_2982_, 2);
v_exprMap_2990_ = lean_ctor_get(v_snd_2982_, 3);
v_recursorRuleMap_2991_ = lean_ctor_get(v_snd_2982_, 4);
v_constMap_2992_ = lean_ctor_get(v_snd_2982_, 5);
v_constOrder_2993_ = lean_ctor_get(v_snd_2982_, 6);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_snd_2982_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2995_ = v_snd_2982_;
v_isShared_2996_ = v_isSharedCheck_3024_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_constOrder_2993_);
lean_inc(v_constMap_2992_);
lean_inc(v_recursorRuleMap_2991_);
lean_inc(v_exprMap_2990_);
lean_inc(v_levelMap_2989_);
lean_inc(v_nameMap_2988_);
lean_inc(v_stream_2987_);
lean_dec(v_snd_2982_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3024_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___x_2997_; 
v___x_2997_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2992_, v_val_2955_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_inc(v_val_2955_);
v___x_2998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2998_, 0, v_val_2955_);
lean_ctor_set(v___x_2998_, 1, v_fst_2965_);
lean_ctor_set(v___x_2998_, 2, v_val_2968_);
v___x_2999_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v_val_2973_);
lean_ctor_set(v___x_2999_, 2, v_fst_2983_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*3, v_b_2942_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set_tag(v___x_2975_, 3);
lean_ctor_set(v___x_2975_, 0, v___x_2999_);
v___x_3001_ = v___x_2975_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3002_ = lean_box(0);
lean_inc(v_val_2955_);
v___x_3003_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2992_, v_val_2955_, v___x_3001_);
v___x_3004_ = lean_array_push(v_constOrder_2993_, v_val_2955_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 6, v___x_3004_);
lean_ctor_set(v___x_2995_, 5, v___x_3003_);
v___x_3006_ = v___x_2995_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_stream_2987_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_nameMap_2988_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_levelMap_2989_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_exprMap_2990_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_recursorRuleMap_2991_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v___x_3006_);
lean_ctor_set(v___x_2985_, 0, v___x_3002_);
v___x_3008_ = v___x_2985_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_3008_);
v___x_3010_ = v___x_2980_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
lean_del_object(v___x_2995_);
lean_dec_ref(v_constOrder_2993_);
lean_dec_ref(v_constMap_2992_);
lean_dec_ref(v_recursorRuleMap_2991_);
lean_dec_ref(v_exprMap_2990_);
lean_dec_ref(v_levelMap_2989_);
lean_dec_ref(v_nameMap_2988_);
lean_dec_ref(v_stream_2987_);
lean_del_object(v___x_2985_);
lean_dec(v_fst_2983_);
lean_dec(v_val_2973_);
lean_dec(v_val_2968_);
lean_dec(v_fst_2965_);
v___x_3015_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2955_, v___x_2997_);
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set_tag(v___x_2975_, 18);
lean_ctor_set(v___x_2975_, 0, v___x_3017_);
v___x_3019_ = v___x_2975_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 1);
lean_ctor_set(v___x_2980_, 0, v___x_3019_);
v___x_3021_ = v___x_2980_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_2975_);
lean_dec(v_val_2973_);
lean_dec(v_val_2968_);
lean_dec(v_fst_2965_);
lean_dec(v_val_2955_);
v_a_3027_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2977_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2977_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec(v___x_2972_);
lean_dec(v_val_2968_);
lean_dec(v_fst_2965_);
lean_dec(v_snd_2964_);
lean_dec(v_val_2955_);
lean_dec_ref(v_elems_2949_);
v___x_3036_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3037_ = l_Nat_reprFast(v_a_2940_);
v___x_3038_ = lean_string_append(v___x_3036_, v___x_3037_);
lean_dec_ref(v___x_3037_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 18);
lean_ctor_set(v___x_2970_, 0, v___x_3038_);
v___x_3040_ = v___x_2970_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 1);
lean_ctor_set(v___x_2962_, 0, v___x_3040_);
v___x_3042_ = v___x_2962_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_dec(v___x_2967_);
lean_dec(v_fst_2965_);
lean_dec(v_snd_2964_);
lean_dec(v_val_2955_);
lean_dec_ref(v_elems_2949_);
lean_dec(v_a_2940_);
v___x_3046_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3047_ = l_Nat_reprFast(v_a_2939_);
v___x_3048_ = lean_string_append(v___x_3046_, v___x_3047_);
lean_dec_ref(v___x_3047_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 18);
lean_ctor_set(v___x_2957_, 0, v___x_3048_);
v___x_3050_ = v___x_2957_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 1);
lean_ctor_set(v___x_2962_, 0, v___x_3050_);
v___x_3052_ = v___x_2962_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_2957_);
lean_dec(v_val_2955_);
lean_dec_ref(v_elems_2949_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
v_a_3056_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2959_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2959_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
lean_dec(v___x_2954_);
lean_dec_ref(v_elems_2949_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_elems_2921_);
lean_dec_ref(v_a_2891_);
v___x_3065_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3066_ = l_Nat_reprFast(v_a_2938_);
v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
lean_dec_ref(v___x_3066_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 18);
lean_ctor_set(v___x_2951_, 0, v___x_3067_);
v___x_3069_ = v___x_2951_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3071_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_3069_);
v___x_3071_ = v___x_2947_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
else
{
lean_del_object(v___x_2947_);
lean_dec(v_val_2945_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_elems_2921_);
lean_dec_ref(v_a_2891_);
goto v___jp_2893_;
}
}
}
else
{
lean_dec(v___x_2944_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_elems_2921_);
lean_dec_ref(v_a_2891_);
goto v___jp_2893_;
}
}
}
}
else
{
lean_dec(v_exponent_2935_);
lean_dec(v_mantissa_2934_);
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2896_;
}
}
else
{
lean_dec(v_val_2932_);
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2896_;
}
}
else
{
lean_dec(v___x_2931_);
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2896_;
}
}
}
else
{
lean_dec(v_exponent_2927_);
lean_dec(v_mantissa_2926_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2899_;
}
}
else
{
lean_dec(v_val_2924_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2899_;
}
}
else
{
lean_dec(v___x_2923_);
lean_dec_ref(v_elems_2921_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2899_;
}
}
else
{
lean_dec(v_val_2920_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2902_;
}
}
else
{
lean_dec(v___x_2919_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2902_;
}
}
}
else
{
lean_dec(v_exponent_2913_);
lean_dec(v_mantissa_2912_);
lean_dec_ref(v_a_2891_);
goto v___jp_2905_;
}
}
else
{
lean_dec(v_val_2910_);
lean_dec_ref(v_a_2891_);
goto v___jp_2905_;
}
}
else
{
lean_dec(v___x_2909_);
lean_dec_ref(v_a_2891_);
goto v___jp_2905_;
}
v___jp_2893_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
v___jp_2896_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
v___jp_2899_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
v___jp_2902_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
v___jp_2905_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___boxed(lean_object* v_data_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_data_3088_, v_a_3089_);
lean_dec(v_data_3088_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(lean_object* v_data_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3100_, v___x_3115_);
if (lean_obj_tag(v___x_3116_) == 1)
{
lean_object* v_val_3117_; 
v_val_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v___x_3116_, 1);
if (lean_obj_tag(v_val_3117_) == 2)
{
lean_object* v_n_3118_; lean_object* v_mantissa_3119_; lean_object* v_exponent_3120_; lean_object* v_natZero_3121_; lean_object* v_intZero_3122_; uint8_t v_isNeg_3123_; 
v_n_3118_ = lean_ctor_get(v_val_3117_, 0);
lean_inc_ref(v_n_3118_);
lean_dec_ref_known(v_val_3117_, 1);
v_mantissa_3119_ = lean_ctor_get(v_n_3118_, 0);
lean_inc(v_mantissa_3119_);
v_exponent_3120_ = lean_ctor_get(v_n_3118_, 1);
lean_inc(v_exponent_3120_);
lean_dec_ref(v_n_3118_);
v_natZero_3121_ = lean_unsigned_to_nat(0u);
v_intZero_3122_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3123_ = lean_int_dec_lt(v_mantissa_3119_, v_intZero_3122_);
if (v_isNeg_3123_ == 0)
{
uint8_t v___x_3124_; 
v___x_3124_ = lean_nat_dec_eq(v_exponent_3120_, v_natZero_3121_);
lean_dec(v_exponent_3120_);
if (v___x_3124_ == 0)
{
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3112_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3100_, v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3126_, 1);
if (lean_obj_tag(v_val_3127_) == 4)
{
lean_object* v_elems_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_elems_3128_ = lean_ctor_get(v_val_3127_, 0);
lean_inc_ref(v_elems_3128_);
lean_dec_ref_known(v_val_3127_, 1);
v___x_3129_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3100_, v___x_3129_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; 
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_val_3131_);
lean_dec_ref_known(v___x_3130_, 1);
if (lean_obj_tag(v_val_3131_) == 2)
{
lean_object* v_n_3132_; lean_object* v_mantissa_3133_; lean_object* v_exponent_3134_; uint8_t v_isNeg_3135_; 
v_n_3132_ = lean_ctor_get(v_val_3131_, 0);
lean_inc_ref(v_n_3132_);
lean_dec_ref_known(v_val_3131_, 1);
v_mantissa_3133_ = lean_ctor_get(v_n_3132_, 0);
lean_inc(v_mantissa_3133_);
v_exponent_3134_ = lean_ctor_get(v_n_3132_, 1);
lean_inc(v_exponent_3134_);
lean_dec_ref(v_n_3132_);
v_isNeg_3135_ = lean_int_dec_lt(v_mantissa_3133_, v_intZero_3122_);
if (v_isNeg_3135_ == 0)
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_eq(v_exponent_3134_, v_natZero_3121_);
lean_dec(v_exponent_3134_);
if (v___x_3136_ == 0)
{
lean_dec(v_mantissa_3133_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3106_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2));
v___x_3138_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3100_, v___x_3137_);
if (lean_obj_tag(v___x_3138_) == 1)
{
lean_object* v_val_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3267_; 
v_val_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3267_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_val_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3267_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
if (lean_obj_tag(v_val_3139_) == 3)
{
lean_object* v_s_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3266_; 
v_s_3143_ = lean_ctor_get(v_val_3139_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_val_3139_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3145_ = v_val_3139_;
v_isShared_3146_ = v_isSharedCheck_3266_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_s_3143_);
lean_dec(v_val_3139_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3266_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_nameMap_3147_; lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_nameMap_3147_ = lean_ctor_get(v_a_3101_, 1);
v_a_3148_ = lean_nat_abs(v_mantissa_3119_);
lean_dec(v_mantissa_3119_);
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3147_, v_a_3148_);
if (lean_obj_tag(v___x_3149_) == 1)
{
lean_object* v_val_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_a_3148_);
lean_del_object(v___x_3141_);
v_val_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3256_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_val_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3256_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3128_, v_a_3101_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3247_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3247_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3247_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_snd_3159_; lean_object* v_fst_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3246_; 
v_snd_3159_ = lean_ctor_get(v_a_3155_, 1);
v_fst_3160_ = lean_ctor_get(v_a_3155_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3162_ = v_a_3155_;
v_isShared_3163_ = v_isSharedCheck_3246_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3159_);
lean_inc(v_fst_3160_);
lean_dec(v_a_3155_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3246_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_stream_3164_; lean_object* v_nameMap_3165_; lean_object* v_levelMap_3166_; lean_object* v_exprMap_3167_; lean_object* v_recursorRuleMap_3168_; lean_object* v_constMap_3169_; lean_object* v_constOrder_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3245_; 
v_stream_3164_ = lean_ctor_get(v_snd_3159_, 0);
v_nameMap_3165_ = lean_ctor_get(v_snd_3159_, 1);
v_levelMap_3166_ = lean_ctor_get(v_snd_3159_, 2);
v_exprMap_3167_ = lean_ctor_get(v_snd_3159_, 3);
v_recursorRuleMap_3168_ = lean_ctor_get(v_snd_3159_, 4);
v_constMap_3169_ = lean_ctor_get(v_snd_3159_, 5);
v_constOrder_3170_ = lean_ctor_get(v_snd_3159_, 6);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_snd_3159_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3172_ = v_snd_3159_;
v_isShared_3173_ = v_isSharedCheck_3245_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_constOrder_3170_);
lean_inc(v_constMap_3169_);
lean_inc(v_recursorRuleMap_3168_);
lean_inc(v_exprMap_3167_);
lean_inc(v_levelMap_3166_);
lean_inc(v_nameMap_3165_);
lean_inc(v_stream_3164_);
lean_dec(v_snd_3159_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3245_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_a_3174_; lean_object* v___x_3175_; 
v_a_3174_ = lean_nat_abs(v_mantissa_3133_);
lean_dec(v_mantissa_3133_);
v___x_3175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3167_, v_a_3174_);
if (lean_obj_tag(v___x_3175_) == 1)
{
lean_object* v_val_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v_a_3174_);
v_val_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3235_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_val_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3235_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
uint8_t v_kind_3181_; lean_object* v_stream_3182_; lean_object* v_nameMap_3183_; lean_object* v_levelMap_3184_; lean_object* v_exprMap_3185_; lean_object* v_recursorRuleMap_3186_; lean_object* v_constMap_3187_; lean_object* v_constOrder_3188_; uint8_t v___x_3216_; 
v___x_3216_ = lean_string_dec_eq(v_s_3143_, v___x_3129_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3218_ = lean_string_dec_eq(v_s_3143_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4));
v___x_3220_ = lean_string_dec_eq(v_s_3143_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5));
v___x_3222_ = lean_string_dec_eq(v_s_3143_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
lean_del_object(v___x_3178_);
lean_dec(v_val_3176_);
lean_del_object(v___x_3172_);
lean_dec_ref(v_constOrder_3170_);
lean_dec_ref(v_constMap_3169_);
lean_dec_ref(v_recursorRuleMap_3168_);
lean_dec_ref(v_exprMap_3167_);
lean_dec_ref(v_levelMap_3166_);
lean_dec_ref(v_nameMap_3165_);
lean_dec_ref(v_stream_3164_);
lean_del_object(v___x_3162_);
lean_dec(v_fst_3160_);
lean_del_object(v___x_3157_);
lean_dec(v_val_3150_);
v___x_3223_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6));
v___x_3224_ = lean_string_append(v___x_3223_, v_s_3143_);
lean_dec_ref(v_s_3143_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 18);
lean_ctor_set(v___x_3152_, 0, v___x_3224_);
v___x_3226_ = v___x_3152_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 1);
lean_ctor_set(v___x_3145_, 0, v___x_3226_);
v___x_3228_ = v___x_3145_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
else
{
uint8_t v___x_3231_; 
lean_del_object(v___x_3152_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
v___x_3231_ = 3;
v_kind_3181_ = v___x_3231_;
v_stream_3182_ = v_stream_3164_;
v_nameMap_3183_ = v_nameMap_3165_;
v_levelMap_3184_ = v_levelMap_3166_;
v_exprMap_3185_ = v_exprMap_3167_;
v_recursorRuleMap_3186_ = v_recursorRuleMap_3168_;
v_constMap_3187_ = v_constMap_3169_;
v_constOrder_3188_ = v_constOrder_3170_;
goto v___jp_3180_;
}
}
else
{
uint8_t v___x_3232_; 
lean_del_object(v___x_3152_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
v___x_3232_ = 2;
v_kind_3181_ = v___x_3232_;
v_stream_3182_ = v_stream_3164_;
v_nameMap_3183_ = v_nameMap_3165_;
v_levelMap_3184_ = v_levelMap_3166_;
v_exprMap_3185_ = v_exprMap_3167_;
v_recursorRuleMap_3186_ = v_recursorRuleMap_3168_;
v_constMap_3187_ = v_constMap_3169_;
v_constOrder_3188_ = v_constOrder_3170_;
goto v___jp_3180_;
}
}
else
{
uint8_t v___x_3233_; 
lean_del_object(v___x_3152_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
v___x_3233_ = 1;
v_kind_3181_ = v___x_3233_;
v_stream_3182_ = v_stream_3164_;
v_nameMap_3183_ = v_nameMap_3165_;
v_levelMap_3184_ = v_levelMap_3166_;
v_exprMap_3185_ = v_exprMap_3167_;
v_recursorRuleMap_3186_ = v_recursorRuleMap_3168_;
v_constMap_3187_ = v_constMap_3169_;
v_constOrder_3188_ = v_constOrder_3170_;
goto v___jp_3180_;
}
}
else
{
uint8_t v___x_3234_; 
lean_del_object(v___x_3152_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
v___x_3234_ = 0;
v_kind_3181_ = v___x_3234_;
v_stream_3182_ = v_stream_3164_;
v_nameMap_3183_ = v_nameMap_3165_;
v_levelMap_3184_ = v_levelMap_3166_;
v_exprMap_3185_ = v_exprMap_3167_;
v_recursorRuleMap_3186_ = v_recursorRuleMap_3168_;
v_constMap_3187_ = v_constMap_3169_;
v_constOrder_3188_ = v_constOrder_3170_;
goto v___jp_3180_;
}
v___jp_3180_:
{
uint8_t v___x_3189_; 
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3187_, v_val_3150_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_inc(v_val_3150_);
v___x_3190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3190_, 0, v_val_3150_);
lean_ctor_set(v___x_3190_, 1, v_fst_3160_);
lean_ctor_set(v___x_3190_, 2, v_val_3176_);
v___x_3191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*1, v_kind_3181_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 4);
lean_ctor_set(v___x_3178_, 0, v___x_3191_);
v___x_3193_ = v___x_3178_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3194_ = lean_box(0);
lean_inc(v_val_3150_);
v___x_3195_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3187_, v_val_3150_, v___x_3193_);
v___x_3196_ = lean_array_push(v_constOrder_3188_, v_val_3150_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 6, v___x_3196_);
lean_ctor_set(v___x_3172_, 5, v___x_3195_);
lean_ctor_set(v___x_3172_, 4, v_recursorRuleMap_3186_);
lean_ctor_set(v___x_3172_, 3, v_exprMap_3185_);
lean_ctor_set(v___x_3172_, 2, v_levelMap_3184_);
lean_ctor_set(v___x_3172_, 1, v_nameMap_3183_);
lean_ctor_set(v___x_3172_, 0, v_stream_3182_);
v___x_3198_ = v___x_3172_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_stream_3182_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_nameMap_3183_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_levelMap_3184_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_exprMap_3185_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_recursorRuleMap_3186_);
lean_ctor_set(v_reuseFailAlloc_3205_, 5, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3205_, 6, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3198_);
lean_ctor_set(v___x_3162_, 0, v___x_3194_);
v___x_3200_ = v___x_3162_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3200_);
v___x_3202_ = v___x_3157_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
lean_dec_ref(v_constOrder_3188_);
lean_dec_ref(v_constMap_3187_);
lean_dec_ref(v_recursorRuleMap_3186_);
lean_dec_ref(v_exprMap_3185_);
lean_dec_ref(v_levelMap_3184_);
lean_dec_ref(v_nameMap_3183_);
lean_dec_ref(v_stream_3182_);
lean_dec(v_val_3176_);
lean_del_object(v___x_3172_);
lean_del_object(v___x_3162_);
lean_dec(v_fst_3160_);
v___x_3207_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3208_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3150_, v___x_3189_);
v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
lean_dec_ref(v___x_3208_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 18);
lean_ctor_set(v___x_3178_, 0, v___x_3209_);
v___x_3211_ = v___x_3178_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 1);
lean_ctor_set(v___x_3157_, 0, v___x_3211_);
v___x_3213_ = v___x_3157_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_dec(v___x_3175_);
lean_del_object(v___x_3172_);
lean_dec_ref(v_constOrder_3170_);
lean_dec_ref(v_constMap_3169_);
lean_dec_ref(v_recursorRuleMap_3168_);
lean_dec_ref(v_exprMap_3167_);
lean_dec_ref(v_levelMap_3166_);
lean_dec_ref(v_nameMap_3165_);
lean_dec_ref(v_stream_3164_);
lean_del_object(v___x_3162_);
lean_dec(v_fst_3160_);
lean_dec(v_val_3150_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
v___x_3236_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3237_ = l_Nat_reprFast(v_a_3174_);
v___x_3238_ = lean_string_append(v___x_3236_, v___x_3237_);
lean_dec_ref(v___x_3237_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 18);
lean_ctor_set(v___x_3152_, 0, v___x_3238_);
v___x_3240_ = v___x_3152_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 1);
lean_ctor_set(v___x_3157_, 0, v___x_3240_);
v___x_3242_ = v___x_3157_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_del_object(v___x_3152_);
lean_dec(v_val_3150_);
lean_del_object(v___x_3145_);
lean_dec_ref(v_s_3143_);
lean_dec(v_mantissa_3133_);
v_a_3248_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3154_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3154_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_dec(v___x_3149_);
lean_dec_ref(v_s_3143_);
lean_dec(v_mantissa_3133_);
lean_dec_ref(v_elems_3128_);
lean_dec_ref(v_a_3101_);
v___x_3257_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3258_ = l_Nat_reprFast(v_a_3148_);
v___x_3259_ = lean_string_append(v___x_3257_, v___x_3258_);
lean_dec_ref(v___x_3258_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 18);
lean_ctor_set(v___x_3145_, 0, v___x_3259_);
v___x_3261_ = v___x_3145_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3261_);
v___x_3263_ = v___x_3141_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
else
{
lean_del_object(v___x_3141_);
lean_dec(v_val_3139_);
lean_dec(v_mantissa_3133_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3103_;
}
}
}
else
{
lean_dec(v___x_3138_);
lean_dec(v_mantissa_3133_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3103_;
}
}
}
else
{
lean_dec(v_exponent_3134_);
lean_dec(v_mantissa_3133_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3106_;
}
}
else
{
lean_dec(v_val_3131_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3106_;
}
}
else
{
lean_dec(v___x_3130_);
lean_dec_ref(v_elems_3128_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3106_;
}
}
else
{
lean_dec(v_val_3127_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3109_;
}
}
else
{
lean_dec(v___x_3126_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3109_;
}
}
}
else
{
lean_dec(v_exponent_3120_);
lean_dec(v_mantissa_3119_);
lean_dec_ref(v_a_3101_);
goto v___jp_3112_;
}
}
else
{
lean_dec(v_val_3117_);
lean_dec_ref(v_a_3101_);
goto v___jp_3112_;
}
}
else
{
lean_dec(v___x_3116_);
lean_dec_ref(v_a_3101_);
goto v___jp_3112_;
}
v___jp_3103_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
v___jp_3106_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
v___jp_3109_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
v___jp_3112_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___boxed(lean_object* v_data_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_data_3268_, v_a_3269_);
lean_dec(v_data_3268_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(lean_object* v_json_3284_, lean_object* v_a_3285_){
_start:
{
if (lean_obj_tag(v_json_3284_) == 5)
{
lean_object* v_kvPairs_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_kvPairs_3320_ = lean_ctor_get(v_json_3284_, 0);
v___x_3321_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3322_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3321_);
if (lean_obj_tag(v___x_3322_) == 1)
{
lean_object* v_val_3323_; 
v_val_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3322_, 1);
if (lean_obj_tag(v_val_3323_) == 2)
{
lean_object* v_n_3324_; lean_object* v_mantissa_3325_; lean_object* v_exponent_3326_; lean_object* v_natZero_3327_; lean_object* v_intZero_3328_; uint8_t v_isNeg_3329_; 
v_n_3324_ = lean_ctor_get(v_val_3323_, 0);
lean_inc_ref(v_n_3324_);
lean_dec_ref_known(v_val_3323_, 1);
v_mantissa_3325_ = lean_ctor_get(v_n_3324_, 0);
lean_inc(v_mantissa_3325_);
v_exponent_3326_ = lean_ctor_get(v_n_3324_, 1);
lean_inc(v_exponent_3326_);
lean_dec_ref(v_n_3324_);
v_natZero_3327_ = lean_unsigned_to_nat(0u);
v_intZero_3328_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3329_ = lean_int_dec_lt(v_mantissa_3325_, v_intZero_3328_);
if (v_isNeg_3329_ == 0)
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_nat_dec_eq(v_exponent_3326_, v_natZero_3327_);
lean_dec(v_exponent_3326_);
if (v___x_3330_ == 0)
{
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3287_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3331_);
if (lean_obj_tag(v___x_3332_) == 1)
{
lean_object* v_val_3333_; 
v_val_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v___x_3332_, 1);
if (lean_obj_tag(v_val_3333_) == 4)
{
lean_object* v_elems_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_elems_3334_ = lean_ctor_get(v_val_3333_, 0);
lean_inc_ref(v_elems_3334_);
lean_dec_ref_known(v_val_3333_, 1);
v___x_3335_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3335_);
if (lean_obj_tag(v___x_3336_) == 1)
{
lean_object* v_val_3337_; 
v_val_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v___x_3336_, 1);
if (lean_obj_tag(v_val_3337_) == 2)
{
lean_object* v_n_3338_; lean_object* v_mantissa_3339_; lean_object* v_exponent_3340_; uint8_t v_isNeg_3341_; 
v_n_3338_ = lean_ctor_get(v_val_3337_, 0);
lean_inc_ref(v_n_3338_);
lean_dec_ref_known(v_val_3337_, 1);
v_mantissa_3339_ = lean_ctor_get(v_n_3338_, 0);
lean_inc(v_mantissa_3339_);
v_exponent_3340_ = lean_ctor_get(v_n_3338_, 1);
lean_inc(v_exponent_3340_);
lean_dec_ref(v_n_3338_);
v_isNeg_3341_ = lean_int_dec_lt(v_mantissa_3339_, v_intZero_3328_);
if (v_isNeg_3341_ == 0)
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_nat_dec_eq(v_exponent_3340_, v_natZero_3327_);
lean_dec(v_exponent_3340_);
if (v___x_3342_ == 0)
{
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3293_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 1)
{
lean_object* v_val_3345_; 
v_val_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3344_, 1);
if (lean_obj_tag(v_val_3345_) == 2)
{
lean_object* v_n_3346_; lean_object* v_mantissa_3347_; lean_object* v_exponent_3348_; uint8_t v_isNeg_3349_; 
v_n_3346_ = lean_ctor_get(v_val_3345_, 0);
lean_inc_ref(v_n_3346_);
lean_dec_ref_known(v_val_3345_, 1);
v_mantissa_3347_ = lean_ctor_get(v_n_3346_, 0);
lean_inc(v_mantissa_3347_);
v_exponent_3348_ = lean_ctor_get(v_n_3346_, 1);
lean_inc(v_exponent_3348_);
lean_dec_ref(v_n_3346_);
v_isNeg_3349_ = lean_int_dec_lt(v_mantissa_3347_, v_intZero_3328_);
if (v_isNeg_3349_ == 0)
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_nat_dec_eq(v_exponent_3348_, v_natZero_3327_);
lean_dec(v_exponent_3348_);
if (v___x_3350_ == 0)
{
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3296_;
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3351_);
if (lean_obj_tag(v___x_3352_) == 1)
{
lean_object* v_val_3353_; 
v_val_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_val_3353_);
lean_dec_ref_known(v___x_3352_, 1);
if (lean_obj_tag(v_val_3353_) == 2)
{
lean_object* v_n_3354_; lean_object* v_mantissa_3355_; lean_object* v_exponent_3356_; uint8_t v_isNeg_3357_; 
v_n_3354_ = lean_ctor_get(v_val_3353_, 0);
lean_inc_ref(v_n_3354_);
lean_dec_ref_known(v_val_3353_, 1);
v_mantissa_3355_ = lean_ctor_get(v_n_3354_, 0);
lean_inc(v_mantissa_3355_);
v_exponent_3356_ = lean_ctor_get(v_n_3354_, 1);
lean_inc(v_exponent_3356_);
lean_dec_ref(v_n_3354_);
v_isNeg_3357_ = lean_int_dec_lt(v_mantissa_3355_, v_intZero_3328_);
if (v_isNeg_3357_ == 0)
{
uint8_t v___x_3358_; 
v___x_3358_ = lean_nat_dec_eq(v_exponent_3356_, v_natZero_3327_);
lean_dec(v_exponent_3356_);
if (v___x_3358_ == 0)
{
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3299_;
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3360_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3359_);
if (lean_obj_tag(v___x_3360_) == 1)
{
lean_object* v_val_3361_; 
v_val_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v___x_3360_, 1);
if (lean_obj_tag(v_val_3361_) == 4)
{
lean_object* v_elems_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_elems_3362_ = lean_ctor_get(v_val_3361_, 0);
lean_inc_ref(v_elems_3362_);
lean_dec_ref_known(v_val_3361_, 1);
v___x_3363_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_3364_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3363_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; 
v_val_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v___x_3364_, 1);
if (lean_obj_tag(v_val_3365_) == 4)
{
lean_object* v_elems_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v_elems_3366_ = lean_ctor_get(v_val_3365_, 0);
lean_inc_ref(v_elems_3366_);
lean_dec_ref_known(v_val_3365_, 1);
v___x_3367_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5));
v___x_3368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3367_);
if (lean_obj_tag(v___x_3368_) == 1)
{
lean_object* v_val_3369_; 
v_val_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3368_, 1);
if (lean_obj_tag(v_val_3369_) == 2)
{
lean_object* v_n_3370_; lean_object* v_mantissa_3371_; lean_object* v_exponent_3372_; uint8_t v_isNeg_3373_; 
v_n_3370_ = lean_ctor_get(v_val_3369_, 0);
lean_inc_ref(v_n_3370_);
lean_dec_ref_known(v_val_3369_, 1);
v_mantissa_3371_ = lean_ctor_get(v_n_3370_, 0);
lean_inc(v_mantissa_3371_);
v_exponent_3372_ = lean_ctor_get(v_n_3370_, 1);
lean_inc(v_exponent_3372_);
lean_dec_ref(v_n_3370_);
v_isNeg_3373_ = lean_int_dec_lt(v_mantissa_3371_, v_intZero_3328_);
if (v_isNeg_3373_ == 0)
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_nat_dec_eq(v_exponent_3372_, v_natZero_3327_);
lean_dec(v_exponent_3372_);
if (v___x_3374_ == 0)
{
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3308_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6));
v___x_3376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3375_);
if (lean_obj_tag(v___x_3376_) == 1)
{
lean_object* v_val_3377_; 
v_val_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_val_3377_);
lean_dec_ref_known(v___x_3376_, 1);
if (lean_obj_tag(v_val_3377_) == 1)
{
uint8_t v_b_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_b_3378_ = lean_ctor_get_uint8(v_val_3377_, 0);
lean_dec_ref_known(v_val_3377_, 0);
v___x_3379_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3380_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3379_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3517_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3517_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_val_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3517_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_val_3381_) == 1)
{
uint8_t v_b_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_b_3385_ = lean_ctor_get_uint8(v_val_3381_, 0);
lean_dec_ref_known(v_val_3381_, 0);
v___x_3386_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7));
v___x_3387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3320_, v___x_3386_);
if (lean_obj_tag(v___x_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3516_; 
v_val_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3516_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3516_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
if (lean_obj_tag(v_val_3388_) == 1)
{
uint8_t v_b_3392_; lean_object* v_nameMap_3393_; lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_b_3392_ = lean_ctor_get_uint8(v_val_3388_, 0);
lean_dec_ref_known(v_val_3388_, 0);
v_nameMap_3393_ = lean_ctor_get(v_a_3285_, 1);
v_a_3394_ = lean_nat_abs(v_mantissa_3325_);
lean_dec(v_mantissa_3325_);
v___x_3395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3393_, v_a_3394_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_a_3394_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3383_);
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3506_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_val_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3506_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3334_, v_a_3285_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3497_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3497_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3497_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_snd_3405_; lean_object* v_fst_3406_; lean_object* v_exprMap_3407_; lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_snd_3405_ = lean_ctor_get(v_a_3401_, 1);
lean_inc(v_snd_3405_);
v_fst_3406_ = lean_ctor_get(v_a_3401_, 0);
lean_inc(v_fst_3406_);
lean_dec(v_a_3401_);
v_exprMap_3407_ = lean_ctor_get(v_snd_3405_, 3);
v_a_3408_ = lean_nat_abs(v_mantissa_3339_);
lean_dec(v_mantissa_3339_);
v___x_3409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3409_) == 1)
{
lean_object* v_val_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_a_3408_);
lean_del_object(v___x_3403_);
lean_del_object(v___x_3398_);
v_val_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3487_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_val_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3487_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3362_, v_snd_3405_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v_fst_3416_; lean_object* v_snd_3417_; lean_object* v___x_3418_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v_fst_3416_ = lean_ctor_get(v_a_3415_, 0);
lean_inc(v_fst_3416_);
v_snd_3417_ = lean_ctor_get(v_a_3415_, 1);
lean_inc(v_snd_3417_);
lean_dec(v_a_3415_);
v___x_3418_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3366_, v_snd_3417_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3470_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_snd_3423_; lean_object* v_fst_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3469_; 
v_snd_3423_ = lean_ctor_get(v_a_3419_, 1);
v_fst_3424_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3426_ = v_a_3419_;
v_isShared_3427_ = v_isSharedCheck_3469_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_snd_3423_);
lean_inc(v_fst_3424_);
lean_dec(v_a_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3469_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_stream_3428_; lean_object* v_nameMap_3429_; lean_object* v_levelMap_3430_; lean_object* v_exprMap_3431_; lean_object* v_recursorRuleMap_3432_; lean_object* v_constMap_3433_; lean_object* v_constOrder_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3468_; 
v_stream_3428_ = lean_ctor_get(v_snd_3423_, 0);
v_nameMap_3429_ = lean_ctor_get(v_snd_3423_, 1);
v_levelMap_3430_ = lean_ctor_get(v_snd_3423_, 2);
v_exprMap_3431_ = lean_ctor_get(v_snd_3423_, 3);
v_recursorRuleMap_3432_ = lean_ctor_get(v_snd_3423_, 4);
v_constMap_3433_ = lean_ctor_get(v_snd_3423_, 5);
v_constOrder_3434_ = lean_ctor_get(v_snd_3423_, 6);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_snd_3423_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3436_ = v_snd_3423_;
v_isShared_3437_ = v_isSharedCheck_3468_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_constOrder_3434_);
lean_inc(v_constMap_3433_);
lean_inc(v_recursorRuleMap_3432_);
lean_inc(v_exprMap_3431_);
lean_inc(v_levelMap_3430_);
lean_inc(v_nameMap_3429_);
lean_inc(v_stream_3428_);
lean_dec(v_snd_3423_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3468_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3433_, v_val_3396_);
if (v___x_3438_ == 0)
{
lean_object* v_a_3439_; lean_object* v_a_3440_; lean_object* v_a_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v_a_3439_ = lean_nat_abs(v_mantissa_3347_);
lean_dec(v_mantissa_3347_);
v_a_3440_ = lean_nat_abs(v_mantissa_3355_);
lean_dec(v_mantissa_3355_);
v_a_3441_ = lean_nat_abs(v_mantissa_3371_);
lean_dec(v_mantissa_3371_);
lean_inc(v_val_3396_);
v___x_3442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3442_, 0, v_val_3396_);
lean_ctor_set(v___x_3442_, 1, v_fst_3406_);
lean_ctor_set(v___x_3442_, 2, v_val_3410_);
v___x_3443_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v_a_3439_);
lean_ctor_set(v___x_3443_, 2, v_a_3440_);
lean_ctor_set(v___x_3443_, 3, v_fst_3416_);
lean_ctor_set(v___x_3443_, 4, v_fst_3424_);
lean_ctor_set(v___x_3443_, 5, v_a_3441_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*6, v_b_3378_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*6 + 1, v_b_3385_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*6 + 2, v_b_3392_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 5);
lean_ctor_set(v___x_3412_, 0, v___x_3443_);
v___x_3445_ = v___x_3412_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3446_ = lean_box(0);
lean_inc(v_val_3396_);
v___x_3447_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3433_, v_val_3396_, v___x_3445_);
v___x_3448_ = lean_array_push(v_constOrder_3434_, v_val_3396_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 6, v___x_3448_);
lean_ctor_set(v___x_3436_, 5, v___x_3447_);
v___x_3450_ = v___x_3436_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_stream_3428_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_nameMap_3429_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_levelMap_3430_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_exprMap_3431_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_recursorRuleMap_3432_);
lean_ctor_set(v_reuseFailAlloc_3457_, 5, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3457_, 6, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___x_3450_);
lean_ctor_set(v___x_3426_, 0, v___x_3446_);
v___x_3452_ = v___x_3426_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3452_);
v___x_3454_ = v___x_3421_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
lean_del_object(v___x_3436_);
lean_dec_ref(v_constOrder_3434_);
lean_dec_ref(v_constMap_3433_);
lean_dec_ref(v_recursorRuleMap_3432_);
lean_dec_ref(v_exprMap_3431_);
lean_dec_ref(v_levelMap_3430_);
lean_dec_ref(v_nameMap_3429_);
lean_dec_ref(v_stream_3428_);
lean_del_object(v___x_3426_);
lean_dec(v_fst_3424_);
lean_dec(v_fst_3416_);
lean_dec(v_val_3410_);
lean_dec(v_fst_3406_);
lean_dec(v_mantissa_3371_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
v___x_3459_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3460_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3396_, v___x_3438_);
v___x_3461_ = lean_string_append(v___x_3459_, v___x_3460_);
lean_dec_ref(v___x_3460_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 18);
lean_ctor_set(v___x_3412_, 0, v___x_3461_);
v___x_3463_ = v___x_3412_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 1);
lean_ctor_set(v___x_3421_, 0, v___x_3463_);
v___x_3465_ = v___x_3421_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_fst_3416_);
lean_del_object(v___x_3412_);
lean_dec(v_val_3410_);
lean_dec(v_fst_3406_);
lean_dec(v_val_3396_);
lean_dec(v_mantissa_3371_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
v_a_3471_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3418_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3418_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3412_);
lean_dec(v_val_3410_);
lean_dec(v_fst_3406_);
lean_dec(v_val_3396_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
v_a_3479_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3414_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3414_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_dec(v___x_3409_);
lean_dec(v_fst_3406_);
lean_dec(v_snd_3405_);
lean_dec(v_val_3396_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
v___x_3488_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3489_ = l_Nat_reprFast(v_a_3408_);
v___x_3490_ = lean_string_append(v___x_3488_, v___x_3489_);
lean_dec_ref(v___x_3489_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 18);
lean_ctor_set(v___x_3398_, 0, v___x_3490_);
v___x_3492_ = v___x_3398_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 1);
lean_ctor_set(v___x_3403_, 0, v___x_3492_);
v___x_3494_ = v___x_3403_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_del_object(v___x_3398_);
lean_dec(v_val_3396_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
v_a_3498_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3400_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3400_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
lean_dec(v___x_3395_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec_ref(v_a_3285_);
v___x_3507_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3508_ = l_Nat_reprFast(v_a_3394_);
v___x_3509_ = lean_string_append(v___x_3507_, v___x_3508_);
lean_dec_ref(v___x_3508_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 18);
lean_ctor_set(v___x_3390_, 0, v___x_3509_);
v___x_3511_ = v___x_3390_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3511_);
v___x_3513_ = v___x_3383_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_del_object(v___x_3390_);
lean_dec(v_val_3388_);
lean_del_object(v___x_3383_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3317_;
}
}
}
else
{
lean_dec(v___x_3387_);
lean_del_object(v___x_3383_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3317_;
}
}
else
{
lean_del_object(v___x_3383_);
lean_dec(v_val_3381_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3314_;
}
}
}
else
{
lean_dec(v___x_3380_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3314_;
}
}
else
{
lean_dec(v_val_3377_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3311_;
}
}
else
{
lean_dec(v___x_3376_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3311_;
}
}
}
else
{
lean_dec(v_exponent_3372_);
lean_dec(v_mantissa_3371_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3308_;
}
}
else
{
lean_dec(v_val_3369_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3308_;
}
}
else
{
lean_dec(v___x_3368_);
lean_dec_ref(v_elems_3366_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3308_;
}
}
else
{
lean_dec(v_val_3365_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3305_;
}
}
else
{
lean_dec(v___x_3364_);
lean_dec_ref(v_elems_3362_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3305_;
}
}
else
{
lean_dec(v_val_3361_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3302_;
}
}
else
{
lean_dec(v___x_3360_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3302_;
}
}
}
else
{
lean_dec(v_exponent_3356_);
lean_dec(v_mantissa_3355_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3299_;
}
}
else
{
lean_dec(v_val_3353_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3299_;
}
}
else
{
lean_dec(v___x_3352_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3299_;
}
}
}
else
{
lean_dec(v_exponent_3348_);
lean_dec(v_mantissa_3347_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3296_;
}
}
else
{
lean_dec(v_val_3345_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3296_;
}
}
else
{
lean_dec(v___x_3344_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3296_;
}
}
}
else
{
lean_dec(v_exponent_3340_);
lean_dec(v_mantissa_3339_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3293_;
}
}
else
{
lean_dec(v_val_3337_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3293_;
}
}
else
{
lean_dec(v___x_3336_);
lean_dec_ref(v_elems_3334_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3293_;
}
}
else
{
lean_dec(v_val_3333_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3290_;
}
}
else
{
lean_dec(v___x_3332_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3290_;
}
}
}
else
{
lean_dec(v_exponent_3326_);
lean_dec(v_mantissa_3325_);
lean_dec_ref(v_a_3285_);
goto v___jp_3287_;
}
}
else
{
lean_dec(v_val_3323_);
lean_dec_ref(v_a_3285_);
goto v___jp_3287_;
}
}
else
{
lean_dec(v___x_3322_);
lean_dec_ref(v_a_3285_);
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref(v_a_3285_);
v___x_3518_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9));
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
v___jp_3287_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
return v___x_3289_;
}
v___jp_3290_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
v___jp_3293_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
v___jp_3296_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
v___jp_3299_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
return v___x_3301_;
}
v___jp_3302_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
v___jp_3305_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
v___jp_3308_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
v___jp_3311_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
v___jp_3314_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
v___jp_3317_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___boxed(lean_object* v_json_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v_json_3520_, v_a_3521_);
lean_dec(v_json_3520_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(lean_object* v_json_3530_, lean_object* v_a_3531_){
_start:
{
if (lean_obj_tag(v_json_3530_) == 5)
{
lean_object* v_kvPairs_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_kvPairs_3557_ = lean_ctor_get(v_json_3530_, 0);
v___x_3558_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3558_);
if (lean_obj_tag(v___x_3559_) == 1)
{
lean_object* v_val_3560_; 
v_val_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_val_3560_);
lean_dec_ref_known(v___x_3559_, 1);
if (lean_obj_tag(v_val_3560_) == 2)
{
lean_object* v_n_3561_; lean_object* v_mantissa_3562_; lean_object* v_exponent_3563_; lean_object* v_natZero_3564_; lean_object* v_intZero_3565_; uint8_t v_isNeg_3566_; 
v_n_3561_ = lean_ctor_get(v_val_3560_, 0);
lean_inc_ref(v_n_3561_);
lean_dec_ref_known(v_val_3560_, 1);
v_mantissa_3562_ = lean_ctor_get(v_n_3561_, 0);
lean_inc(v_mantissa_3562_);
v_exponent_3563_ = lean_ctor_get(v_n_3561_, 1);
lean_inc(v_exponent_3563_);
lean_dec_ref(v_n_3561_);
v_natZero_3564_ = lean_unsigned_to_nat(0u);
v_intZero_3565_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3566_ = lean_int_dec_lt(v_mantissa_3562_, v_intZero_3565_);
if (v_isNeg_3566_ == 0)
{
uint8_t v___x_3567_; 
v___x_3567_ = lean_nat_dec_eq(v_exponent_3563_, v_natZero_3564_);
lean_dec(v_exponent_3563_);
if (v___x_3567_ == 0)
{
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3533_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3568_);
if (lean_obj_tag(v___x_3569_) == 1)
{
lean_object* v_val_3570_; 
v_val_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_val_3570_);
lean_dec_ref_known(v___x_3569_, 1);
if (lean_obj_tag(v_val_3570_) == 4)
{
lean_object* v_elems_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_elems_3571_ = lean_ctor_get(v_val_3570_, 0);
lean_inc_ref(v_elems_3571_);
lean_dec_ref_known(v_val_3570_, 1);
v___x_3572_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3572_);
if (lean_obj_tag(v___x_3573_) == 1)
{
lean_object* v_val_3574_; 
v_val_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v___x_3573_, 1);
if (lean_obj_tag(v_val_3574_) == 2)
{
lean_object* v_n_3575_; lean_object* v_mantissa_3576_; lean_object* v_exponent_3577_; uint8_t v_isNeg_3578_; 
v_n_3575_ = lean_ctor_get(v_val_3574_, 0);
lean_inc_ref(v_n_3575_);
lean_dec_ref_known(v_val_3574_, 1);
v_mantissa_3576_ = lean_ctor_get(v_n_3575_, 0);
lean_inc(v_mantissa_3576_);
v_exponent_3577_ = lean_ctor_get(v_n_3575_, 1);
lean_inc(v_exponent_3577_);
lean_dec_ref(v_n_3575_);
v_isNeg_3578_ = lean_int_dec_lt(v_mantissa_3576_, v_intZero_3565_);
if (v_isNeg_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = lean_nat_dec_eq(v_exponent_3577_, v_natZero_3564_);
lean_dec(v_exponent_3577_);
if (v___x_3579_ == 0)
{
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3539_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2));
v___x_3581_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3580_);
if (lean_obj_tag(v___x_3581_) == 1)
{
lean_object* v_val_3582_; 
v_val_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v___x_3581_, 1);
if (lean_obj_tag(v_val_3582_) == 2)
{
lean_object* v_n_3583_; lean_object* v_mantissa_3584_; lean_object* v_exponent_3585_; uint8_t v_isNeg_3586_; 
v_n_3583_ = lean_ctor_get(v_val_3582_, 0);
lean_inc_ref(v_n_3583_);
lean_dec_ref_known(v_val_3582_, 1);
v_mantissa_3584_ = lean_ctor_get(v_n_3583_, 0);
lean_inc(v_mantissa_3584_);
v_exponent_3585_ = lean_ctor_get(v_n_3583_, 1);
lean_inc(v_exponent_3585_);
lean_dec_ref(v_n_3583_);
v_isNeg_3586_ = lean_int_dec_lt(v_mantissa_3584_, v_intZero_3565_);
if (v_isNeg_3586_ == 0)
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_nat_dec_eq(v_exponent_3585_, v_natZero_3564_);
lean_dec(v_exponent_3585_);
if (v___x_3587_ == 0)
{
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3542_;
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3));
v___x_3589_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3588_);
if (lean_obj_tag(v___x_3589_) == 1)
{
lean_object* v_val_3590_; 
v_val_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_val_3590_);
lean_dec_ref_known(v___x_3589_, 1);
if (lean_obj_tag(v_val_3590_) == 2)
{
lean_object* v_n_3591_; lean_object* v_mantissa_3592_; lean_object* v_exponent_3593_; uint8_t v_isNeg_3594_; 
v_n_3591_ = lean_ctor_get(v_val_3590_, 0);
lean_inc_ref(v_n_3591_);
lean_dec_ref_known(v_val_3590_, 1);
v_mantissa_3592_ = lean_ctor_get(v_n_3591_, 0);
lean_inc(v_mantissa_3592_);
v_exponent_3593_ = lean_ctor_get(v_n_3591_, 1);
lean_inc(v_exponent_3593_);
lean_dec_ref(v_n_3591_);
v_isNeg_3594_ = lean_int_dec_lt(v_mantissa_3592_, v_intZero_3565_);
if (v_isNeg_3594_ == 0)
{
uint8_t v___x_3595_; 
v___x_3595_ = lean_nat_dec_eq(v_exponent_3593_, v_natZero_3564_);
lean_dec(v_exponent_3593_);
if (v___x_3595_ == 0)
{
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3545_;
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3597_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3596_);
if (lean_obj_tag(v___x_3597_) == 1)
{
lean_object* v_val_3598_; 
v_val_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_val_3598_);
lean_dec_ref_known(v___x_3597_, 1);
if (lean_obj_tag(v_val_3598_) == 2)
{
lean_object* v_n_3599_; lean_object* v_mantissa_3600_; lean_object* v_exponent_3601_; uint8_t v_isNeg_3602_; 
v_n_3599_ = lean_ctor_get(v_val_3598_, 0);
lean_inc_ref(v_n_3599_);
lean_dec_ref_known(v_val_3598_, 1);
v_mantissa_3600_ = lean_ctor_get(v_n_3599_, 0);
lean_inc(v_mantissa_3600_);
v_exponent_3601_ = lean_ctor_get(v_n_3599_, 1);
lean_inc(v_exponent_3601_);
lean_dec_ref(v_n_3599_);
v_isNeg_3602_ = lean_int_dec_lt(v_mantissa_3600_, v_intZero_3565_);
if (v_isNeg_3602_ == 0)
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_nat_dec_eq(v_exponent_3601_, v_natZero_3564_);
lean_dec(v_exponent_3601_);
if (v___x_3603_ == 0)
{
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3548_;
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4));
v___x_3605_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3604_);
if (lean_obj_tag(v___x_3605_) == 1)
{
lean_object* v_val_3606_; 
v_val_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v___x_3605_, 1);
if (lean_obj_tag(v_val_3606_) == 2)
{
lean_object* v_n_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3733_; 
v_n_3607_ = lean_ctor_get(v_val_3606_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_val_3606_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3609_ = v_val_3606_;
v_isShared_3610_ = v_isSharedCheck_3733_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_n_3607_);
lean_dec(v_val_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3733_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_mantissa_3611_; lean_object* v_exponent_3612_; uint8_t v_isNeg_3613_; 
v_mantissa_3611_ = lean_ctor_get(v_n_3607_, 0);
lean_inc(v_mantissa_3611_);
v_exponent_3612_ = lean_ctor_get(v_n_3607_, 1);
lean_inc(v_exponent_3612_);
lean_dec_ref(v_n_3607_);
v_isNeg_3613_ = lean_int_dec_lt(v_mantissa_3611_, v_intZero_3565_);
if (v_isNeg_3613_ == 0)
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_nat_dec_eq(v_exponent_3612_, v_natZero_3564_);
lean_dec(v_exponent_3612_);
if (v___x_3614_ == 0)
{
lean_dec(v_mantissa_3611_);
lean_del_object(v___x_3609_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3551_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3557_, v___x_3615_);
if (lean_obj_tag(v___x_3616_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3732_; 
v_val_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3732_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_val_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3732_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
if (lean_obj_tag(v_val_3617_) == 1)
{
uint8_t v_b_3621_; lean_object* v_nameMap_3622_; lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_b_3621_ = lean_ctor_get_uint8(v_val_3617_, 0);
lean_dec_ref_known(v_val_3617_, 0);
v_nameMap_3622_ = lean_ctor_get(v_a_3531_, 1);
v_a_3623_ = lean_nat_abs(v_mantissa_3562_);
lean_dec(v_mantissa_3562_);
v___x_3624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3622_, v_a_3623_);
if (lean_obj_tag(v___x_3624_) == 1)
{
lean_object* v_val_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_a_3623_);
lean_del_object(v___x_3619_);
lean_del_object(v___x_3609_);
v_val_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3722_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_val_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3722_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3571_, v_a_3531_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3713_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3713_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3713_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_snd_3634_; lean_object* v_fst_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3712_; 
v_snd_3634_ = lean_ctor_get(v_a_3630_, 1);
v_fst_3635_ = lean_ctor_get(v_a_3630_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_a_3630_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3637_ = v_a_3630_;
v_isShared_3638_ = v_isSharedCheck_3712_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3635_);
lean_dec(v_a_3630_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3712_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_stream_3639_; lean_object* v_nameMap_3640_; lean_object* v_levelMap_3641_; lean_object* v_exprMap_3642_; lean_object* v_recursorRuleMap_3643_; lean_object* v_constMap_3644_; lean_object* v_constOrder_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3711_; 
v_stream_3639_ = lean_ctor_get(v_snd_3634_, 0);
v_nameMap_3640_ = lean_ctor_get(v_snd_3634_, 1);
v_levelMap_3641_ = lean_ctor_get(v_snd_3634_, 2);
v_exprMap_3642_ = lean_ctor_get(v_snd_3634_, 3);
v_recursorRuleMap_3643_ = lean_ctor_get(v_snd_3634_, 4);
v_constMap_3644_ = lean_ctor_get(v_snd_3634_, 5);
v_constOrder_3645_ = lean_ctor_get(v_snd_3634_, 6);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_snd_3634_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3647_ = v_snd_3634_;
v_isShared_3648_ = v_isSharedCheck_3711_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_constOrder_3645_);
lean_inc(v_constMap_3644_);
lean_inc(v_recursorRuleMap_3643_);
lean_inc(v_exprMap_3642_);
lean_inc(v_levelMap_3641_);
lean_inc(v_nameMap_3640_);
lean_inc(v_stream_3639_);
lean_dec(v_snd_3634_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3711_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v_a_3649_; lean_object* v___x_3650_; 
v_a_3649_ = lean_nat_abs(v_mantissa_3576_);
lean_dec(v_mantissa_3576_);
v___x_3650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3642_, v_a_3649_);
if (lean_obj_tag(v___x_3650_) == 1)
{
lean_object* v_val_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v_a_3649_);
lean_del_object(v___x_3627_);
v_val_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_val_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_a_3655_; lean_object* v___x_3656_; 
v_a_3655_ = lean_nat_abs(v_mantissa_3584_);
lean_dec(v_mantissa_3584_);
v___x_3656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3640_, v_a_3655_);
if (lean_obj_tag(v___x_3656_) == 1)
{
lean_object* v_val_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v_a_3655_);
lean_del_object(v___x_3653_);
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3691_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_val_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3691_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
uint8_t v___x_3661_; 
v___x_3661_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3644_, v_val_3625_);
if (v___x_3661_ == 0)
{
lean_object* v_a_3662_; lean_object* v_a_3663_; lean_object* v_a_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
v_a_3662_ = lean_nat_abs(v_mantissa_3592_);
lean_dec(v_mantissa_3592_);
v_a_3663_ = lean_nat_abs(v_mantissa_3600_);
lean_dec(v_mantissa_3600_);
v_a_3664_ = lean_nat_abs(v_mantissa_3611_);
lean_dec(v_mantissa_3611_);
lean_inc(v_val_3625_);
v___x_3665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3665_, 0, v_val_3625_);
lean_ctor_set(v___x_3665_, 1, v_fst_3635_);
lean_ctor_set(v___x_3665_, 2, v_val_3651_);
v___x_3666_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v_val_3657_);
lean_ctor_set(v___x_3666_, 2, v_a_3662_);
lean_ctor_set(v___x_3666_, 3, v_a_3663_);
lean_ctor_set(v___x_3666_, 4, v_a_3664_);
lean_ctor_set_uint8(v___x_3666_, sizeof(void*)*5, v_b_3621_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 6);
lean_ctor_set(v___x_3659_, 0, v___x_3666_);
v___x_3668_ = v___x_3659_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3669_ = lean_box(0);
lean_inc(v_val_3625_);
v___x_3670_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3644_, v_val_3625_, v___x_3668_);
v___x_3671_ = lean_array_push(v_constOrder_3645_, v_val_3625_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 6, v___x_3671_);
lean_ctor_set(v___x_3647_, 5, v___x_3670_);
v___x_3673_ = v___x_3647_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_stream_3639_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_nameMap_3640_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_levelMap_3641_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_exprMap_3642_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_recursorRuleMap_3643_);
lean_ctor_set(v_reuseFailAlloc_3680_, 5, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3680_, 6, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 1, v___x_3673_);
lean_ctor_set(v___x_3637_, 0, v___x_3669_);
v___x_3675_ = v___x_3637_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3675_);
v___x_3677_ = v___x_3632_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_val_3657_);
lean_dec(v_val_3651_);
lean_del_object(v___x_3647_);
lean_dec_ref(v_constOrder_3645_);
lean_dec_ref(v_constMap_3644_);
lean_dec_ref(v_recursorRuleMap_3643_);
lean_dec_ref(v_exprMap_3642_);
lean_dec_ref(v_levelMap_3641_);
lean_dec_ref(v_nameMap_3640_);
lean_dec_ref(v_stream_3639_);
lean_del_object(v___x_3637_);
lean_dec(v_fst_3635_);
lean_dec(v_mantissa_3611_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
v___x_3682_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3625_, v___x_3661_);
v___x_3684_ = lean_string_append(v___x_3682_, v___x_3683_);
lean_dec_ref(v___x_3683_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 18);
lean_ctor_set(v___x_3659_, 0, v___x_3684_);
v___x_3686_ = v___x_3659_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3688_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3686_);
v___x_3688_ = v___x_3632_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
lean_dec(v___x_3656_);
lean_dec(v_val_3651_);
lean_del_object(v___x_3647_);
lean_dec_ref(v_constOrder_3645_);
lean_dec_ref(v_constMap_3644_);
lean_dec_ref(v_recursorRuleMap_3643_);
lean_dec_ref(v_exprMap_3642_);
lean_dec_ref(v_levelMap_3641_);
lean_dec_ref(v_nameMap_3640_);
lean_dec_ref(v_stream_3639_);
lean_del_object(v___x_3637_);
lean_dec(v_fst_3635_);
lean_dec(v_val_3625_);
lean_dec(v_mantissa_3611_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
v___x_3692_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3693_ = l_Nat_reprFast(v_a_3655_);
v___x_3694_ = lean_string_append(v___x_3692_, v___x_3693_);
lean_dec_ref(v___x_3693_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 18);
lean_ctor_set(v___x_3653_, 0, v___x_3694_);
v___x_3696_ = v___x_3653_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3696_);
v___x_3698_ = v___x_3632_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec(v___x_3650_);
lean_del_object(v___x_3647_);
lean_dec_ref(v_constOrder_3645_);
lean_dec_ref(v_constMap_3644_);
lean_dec_ref(v_recursorRuleMap_3643_);
lean_dec_ref(v_exprMap_3642_);
lean_dec_ref(v_levelMap_3641_);
lean_dec_ref(v_nameMap_3640_);
lean_dec_ref(v_stream_3639_);
lean_del_object(v___x_3637_);
lean_dec(v_fst_3635_);
lean_dec(v_val_3625_);
lean_dec(v_mantissa_3611_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
v___x_3702_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3703_ = l_Nat_reprFast(v_a_3649_);
v___x_3704_ = lean_string_append(v___x_3702_, v___x_3703_);
lean_dec_ref(v___x_3703_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 18);
lean_ctor_set(v___x_3627_, 0, v___x_3704_);
v___x_3706_ = v___x_3627_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3708_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3706_);
v___x_3708_ = v___x_3632_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_del_object(v___x_3627_);
lean_dec(v_val_3625_);
lean_dec(v_mantissa_3611_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
v_a_3714_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3629_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3629_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_dec(v___x_3624_);
lean_dec(v_mantissa_3611_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec_ref(v_a_3531_);
v___x_3723_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3724_ = l_Nat_reprFast(v_a_3623_);
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
lean_dec_ref(v___x_3724_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 18);
lean_ctor_set(v___x_3619_, 0, v___x_3725_);
v___x_3727_ = v___x_3619_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 1);
lean_ctor_set(v___x_3609_, 0, v___x_3727_);
v___x_3729_ = v___x_3609_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_del_object(v___x_3619_);
lean_dec(v_val_3617_);
lean_dec(v_mantissa_3611_);
lean_del_object(v___x_3609_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3554_;
}
}
}
else
{
lean_dec(v___x_3616_);
lean_dec(v_mantissa_3611_);
lean_del_object(v___x_3609_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3554_;
}
}
}
else
{
lean_dec(v_exponent_3612_);
lean_dec(v_mantissa_3611_);
lean_del_object(v___x_3609_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3551_;
}
}
}
else
{
lean_dec(v_val_3606_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3551_;
}
}
else
{
lean_dec(v___x_3605_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3551_;
}
}
}
else
{
lean_dec(v_exponent_3601_);
lean_dec(v_mantissa_3600_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3548_;
}
}
else
{
lean_dec(v_val_3598_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3548_;
}
}
else
{
lean_dec(v___x_3597_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3548_;
}
}
}
else
{
lean_dec(v_exponent_3593_);
lean_dec(v_mantissa_3592_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3545_;
}
}
else
{
lean_dec(v_val_3590_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3545_;
}
}
else
{
lean_dec(v___x_3589_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3545_;
}
}
}
else
{
lean_dec(v_exponent_3585_);
lean_dec(v_mantissa_3584_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3542_;
}
}
else
{
lean_dec(v_val_3582_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3542_;
}
}
else
{
lean_dec(v___x_3581_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3542_;
}
}
}
else
{
lean_dec(v_exponent_3577_);
lean_dec(v_mantissa_3576_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3539_;
}
}
else
{
lean_dec(v_val_3574_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3539_;
}
}
else
{
lean_dec(v___x_3573_);
lean_dec_ref(v_elems_3571_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3539_;
}
}
else
{
lean_dec(v_val_3570_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3536_;
}
}
else
{
lean_dec(v___x_3569_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3536_;
}
}
}
else
{
lean_dec(v_exponent_3563_);
lean_dec(v_mantissa_3562_);
lean_dec_ref(v_a_3531_);
goto v___jp_3533_;
}
}
else
{
lean_dec(v_val_3560_);
lean_dec_ref(v_a_3531_);
goto v___jp_3533_;
}
}
else
{
lean_dec(v___x_3559_);
lean_dec_ref(v_a_3531_);
goto v___jp_3533_;
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec_ref(v_a_3531_);
v___x_3734_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
v___jp_3533_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
return v___x_3535_;
}
v___jp_3536_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
return v___x_3538_;
}
v___jp_3539_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
v___jp_3542_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
v___jp_3545_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
return v___x_3547_;
}
v___jp_3548_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
v___jp_3551_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
return v___x_3553_;
}
v___jp_3554_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___boxed(lean_object* v_json_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v_json_3736_, v_a_3737_);
lean_dec(v_json_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(lean_object* v_x_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = l_List_reverse___redArg(v_x_3746_);
v___x_3759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___y_3747_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
else
{
lean_object* v_head_3761_; 
v_head_3761_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_head_3761_);
if (lean_obj_tag(v_head_3761_) == 5)
{
lean_object* v_tail_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3837_; 
v_tail_3762_ = lean_ctor_get(v_x_3745_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_x_3745_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_x_3745_, 0);
lean_dec(v_unused_3838_);
v___x_3764_ = v_x_3745_;
v_isShared_3765_ = v_isSharedCheck_3837_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_tail_3762_);
lean_dec(v_x_3745_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3837_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_kvPairs_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v_kvPairs_3766_ = lean_ctor_get(v_head_3761_, 0);
lean_inc(v_kvPairs_3766_);
lean_dec_ref_known(v_head_3761_, 1);
v___x_3767_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3768_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3766_, v___x_3767_);
if (lean_obj_tag(v___x_3768_) == 1)
{
lean_object* v_val_3769_; 
v_val_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_val_3769_);
lean_dec_ref_known(v___x_3768_, 1);
if (lean_obj_tag(v_val_3769_) == 2)
{
lean_object* v_n_3770_; lean_object* v_mantissa_3771_; lean_object* v_exponent_3772_; lean_object* v_natZero_3773_; lean_object* v_intZero_3774_; uint8_t v_isNeg_3775_; 
v_n_3770_ = lean_ctor_get(v_val_3769_, 0);
lean_inc_ref(v_n_3770_);
lean_dec_ref_known(v_val_3769_, 1);
v_mantissa_3771_ = lean_ctor_get(v_n_3770_, 0);
lean_inc(v_mantissa_3771_);
v_exponent_3772_ = lean_ctor_get(v_n_3770_, 1);
lean_inc(v_exponent_3772_);
lean_dec_ref(v_n_3770_);
v_natZero_3773_ = lean_unsigned_to_nat(0u);
v_intZero_3774_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3775_ = lean_int_dec_lt(v_mantissa_3771_, v_intZero_3774_);
if (v_isNeg_3775_ == 0)
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_nat_dec_eq(v_exponent_3772_, v_natZero_3773_);
lean_dec(v_exponent_3772_);
if (v___x_3776_ == 0)
{
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3749_;
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2));
v___x_3778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3766_, v___x_3777_);
if (lean_obj_tag(v___x_3778_) == 1)
{
lean_object* v_val_3779_; 
v_val_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_val_3779_);
lean_dec_ref_known(v___x_3778_, 1);
if (lean_obj_tag(v_val_3779_) == 2)
{
lean_object* v_n_3780_; lean_object* v_mantissa_3781_; lean_object* v_exponent_3782_; uint8_t v_isNeg_3783_; 
v_n_3780_ = lean_ctor_get(v_val_3779_, 0);
lean_inc_ref(v_n_3780_);
lean_dec_ref_known(v_val_3779_, 1);
v_mantissa_3781_ = lean_ctor_get(v_n_3780_, 0);
lean_inc(v_mantissa_3781_);
v_exponent_3782_ = lean_ctor_get(v_n_3780_, 1);
lean_inc(v_exponent_3782_);
lean_dec_ref(v_n_3780_);
v_isNeg_3783_ = lean_int_dec_lt(v_mantissa_3781_, v_intZero_3774_);
if (v_isNeg_3783_ == 0)
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_nat_dec_eq(v_exponent_3782_, v_natZero_3773_);
lean_dec(v_exponent_3782_);
if (v___x_3784_ == 0)
{
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3752_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3));
v___x_3786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3766_, v___x_3785_);
lean_dec(v_kvPairs_3766_);
if (lean_obj_tag(v___x_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3836_; 
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3836_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_val_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3836_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_val_3787_) == 2)
{
lean_object* v_n_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3835_; 
v_n_3791_ = lean_ctor_get(v_val_3787_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_val_3787_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3793_ = v_val_3787_;
v_isShared_3794_ = v_isSharedCheck_3835_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_n_3791_);
lean_dec(v_val_3787_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3835_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v_mantissa_3795_; lean_object* v_exponent_3796_; uint8_t v_isNeg_3797_; 
v_mantissa_3795_ = lean_ctor_get(v_n_3791_, 0);
lean_inc(v_mantissa_3795_);
v_exponent_3796_ = lean_ctor_get(v_n_3791_, 1);
lean_inc(v_exponent_3796_);
lean_dec_ref(v_n_3791_);
v_isNeg_3797_ = lean_int_dec_lt(v_mantissa_3795_, v_intZero_3774_);
if (v_isNeg_3797_ == 0)
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_nat_dec_eq(v_exponent_3796_, v_natZero_3773_);
lean_dec(v_exponent_3796_);
if (v___x_3798_ == 0)
{
lean_dec(v_mantissa_3795_);
lean_del_object(v___x_3793_);
lean_del_object(v___x_3789_);
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3755_;
}
else
{
lean_object* v_nameMap_3799_; lean_object* v_exprMap_3800_; lean_object* v_a_3801_; lean_object* v___x_3802_; 
v_nameMap_3799_ = lean_ctor_get(v___y_3747_, 1);
v_exprMap_3800_ = lean_ctor_get(v___y_3747_, 3);
v_a_3801_ = lean_nat_abs(v_mantissa_3771_);
lean_dec(v_mantissa_3771_);
v___x_3802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3799_, v_a_3801_);
if (lean_obj_tag(v___x_3802_) == 1)
{
lean_object* v_val_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_a_3801_);
lean_del_object(v___x_3789_);
v_val_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3825_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_val_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3825_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_a_3807_; lean_object* v___x_3808_; 
v_a_3807_ = lean_nat_abs(v_mantissa_3795_);
lean_dec(v_mantissa_3795_);
v___x_3808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3800_, v_a_3807_);
if (lean_obj_tag(v___x_3808_) == 1)
{
lean_object* v_val_3809_; lean_object* v_a_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
lean_dec(v_a_3807_);
lean_del_object(v___x_3805_);
lean_del_object(v___x_3793_);
v_val_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v_a_3810_ = lean_nat_abs(v_mantissa_3781_);
lean_dec(v_mantissa_3781_);
v___x_3811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3811_, 0, v_val_3803_);
lean_ctor_set(v___x_3811_, 1, v_a_3810_);
lean_ctor_set(v___x_3811_, 2, v_val_3809_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v_x_3746_);
lean_ctor_set(v___x_3764_, 0, v___x_3811_);
v___x_3813_ = v___x_3764_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_x_3746_);
v___x_3813_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
v_x_3745_ = v_tail_3762_;
v_x_3746_ = v___x_3813_;
goto _start;
}
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
lean_dec(v___x_3808_);
lean_dec(v_val_3803_);
lean_dec(v_mantissa_3781_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
v___x_3816_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3817_ = l_Nat_reprFast(v_a_3807_);
v___x_3818_ = lean_string_append(v___x_3816_, v___x_3817_);
lean_dec_ref(v___x_3817_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 18);
lean_ctor_set(v___x_3805_, 0, v___x_3818_);
v___x_3820_ = v___x_3805_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3822_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 1);
lean_ctor_set(v___x_3793_, 0, v___x_3820_);
v___x_3822_ = v___x_3793_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec(v___x_3802_);
lean_dec(v_mantissa_3795_);
lean_dec(v_mantissa_3781_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
v___x_3826_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3827_ = l_Nat_reprFast(v_a_3801_);
v___x_3828_ = lean_string_append(v___x_3826_, v___x_3827_);
lean_dec_ref(v___x_3827_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 18);
lean_ctor_set(v___x_3793_, 0, v___x_3828_);
v___x_3830_ = v___x_3793_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3832_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3830_);
v___x_3832_ = v___x_3789_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
else
{
lean_dec(v_exponent_3796_);
lean_dec(v_mantissa_3795_);
lean_del_object(v___x_3793_);
lean_del_object(v___x_3789_);
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3755_;
}
}
}
else
{
lean_del_object(v___x_3789_);
lean_dec(v_val_3787_);
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3755_;
}
}
}
else
{
lean_dec(v___x_3786_);
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3755_;
}
}
}
else
{
lean_dec(v_exponent_3782_);
lean_dec(v_mantissa_3781_);
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3752_;
}
}
else
{
lean_dec(v_val_3779_);
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3752_;
}
}
else
{
lean_dec(v___x_3778_);
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3752_;
}
}
}
else
{
lean_dec(v_exponent_3772_);
lean_dec(v_mantissa_3771_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3749_;
}
}
else
{
lean_dec(v_val_3769_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3749_;
}
}
else
{
lean_dec(v___x_3768_);
lean_dec(v_kvPairs_3766_);
lean_del_object(v___x_3764_);
lean_dec(v_tail_3762_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
goto v___jp_3749_;
}
}
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_dec_ref_known(v_x_3745_, 2);
lean_dec(v_head_3761_);
lean_dec_ref(v___y_3747_);
lean_dec(v_x_3746_);
v___x_3839_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
}
v___jp_3749_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
v___jp_3752_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
v___jp_3755_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
return v___x_3757_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___boxed(lean_object* v_x_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v_x_3841_, v_x_3842_, v___y_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(lean_object* v_json_3850_, lean_object* v_a_3851_){
_start:
{
if (lean_obj_tag(v_json_3850_) == 5)
{
lean_object* v_kvPairs_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_kvPairs_3886_ = lean_ctor_get(v_json_3850_, 0);
v___x_3887_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3888_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3887_);
if (lean_obj_tag(v___x_3888_) == 1)
{
lean_object* v_val_3889_; 
v_val_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v___x_3888_, 1);
if (lean_obj_tag(v_val_3889_) == 2)
{
lean_object* v_n_3890_; lean_object* v_mantissa_3891_; lean_object* v_exponent_3892_; lean_object* v_natZero_3893_; lean_object* v_intZero_3894_; uint8_t v_isNeg_3895_; 
v_n_3890_ = lean_ctor_get(v_val_3889_, 0);
lean_inc_ref(v_n_3890_);
lean_dec_ref_known(v_val_3889_, 1);
v_mantissa_3891_ = lean_ctor_get(v_n_3890_, 0);
lean_inc(v_mantissa_3891_);
v_exponent_3892_ = lean_ctor_get(v_n_3890_, 1);
lean_inc(v_exponent_3892_);
lean_dec_ref(v_n_3890_);
v_natZero_3893_ = lean_unsigned_to_nat(0u);
v_intZero_3894_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3895_ = lean_int_dec_lt(v_mantissa_3891_, v_intZero_3894_);
if (v_isNeg_3895_ == 0)
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_eq(v_exponent_3892_, v_natZero_3893_);
lean_dec(v_exponent_3892_);
if (v___x_3896_ == 0)
{
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3853_;
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3898_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3897_);
if (lean_obj_tag(v___x_3898_) == 1)
{
lean_object* v_val_3899_; 
v_val_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v___x_3898_, 1);
if (lean_obj_tag(v_val_3899_) == 4)
{
lean_object* v_elems_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_elems_3900_ = lean_ctor_get(v_val_3899_, 0);
lean_inc_ref(v_elems_3900_);
lean_dec_ref_known(v_val_3899_, 1);
v___x_3901_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3902_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3901_);
if (lean_obj_tag(v___x_3902_) == 1)
{
lean_object* v_val_3903_; 
v_val_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_val_3903_);
lean_dec_ref_known(v___x_3902_, 1);
if (lean_obj_tag(v_val_3903_) == 2)
{
lean_object* v_n_3904_; lean_object* v_mantissa_3905_; lean_object* v_exponent_3906_; uint8_t v_isNeg_3907_; 
v_n_3904_ = lean_ctor_get(v_val_3903_, 0);
lean_inc_ref(v_n_3904_);
lean_dec_ref_known(v_val_3903_, 1);
v_mantissa_3905_ = lean_ctor_get(v_n_3904_, 0);
lean_inc(v_mantissa_3905_);
v_exponent_3906_ = lean_ctor_get(v_n_3904_, 1);
lean_inc(v_exponent_3906_);
lean_dec_ref(v_n_3904_);
v_isNeg_3907_ = lean_int_dec_lt(v_mantissa_3905_, v_intZero_3894_);
if (v_isNeg_3907_ == 0)
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_nat_dec_eq(v_exponent_3906_, v_natZero_3893_);
lean_dec(v_exponent_3906_);
if (v___x_3908_ == 0)
{
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3859_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3910_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3909_);
if (lean_obj_tag(v___x_3910_) == 1)
{
lean_object* v_val_3911_; 
v_val_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v___x_3910_, 1);
if (lean_obj_tag(v_val_3911_) == 4)
{
lean_object* v_elems_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_elems_3912_ = lean_ctor_get(v_val_3911_, 0);
lean_inc_ref(v_elems_3912_);
lean_dec_ref_known(v_val_3911_, 1);
v___x_3913_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3914_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3913_);
if (lean_obj_tag(v___x_3914_) == 1)
{
lean_object* v_val_3915_; 
v_val_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_val_3915_);
lean_dec_ref_known(v___x_3914_, 1);
if (lean_obj_tag(v_val_3915_) == 2)
{
lean_object* v_n_3916_; lean_object* v_mantissa_3917_; lean_object* v_exponent_3918_; uint8_t v_isNeg_3919_; 
v_n_3916_ = lean_ctor_get(v_val_3915_, 0);
lean_inc_ref(v_n_3916_);
lean_dec_ref_known(v_val_3915_, 1);
v_mantissa_3917_ = lean_ctor_get(v_n_3916_, 0);
lean_inc(v_mantissa_3917_);
v_exponent_3918_ = lean_ctor_get(v_n_3916_, 1);
lean_inc(v_exponent_3918_);
lean_dec_ref(v_n_3916_);
v_isNeg_3919_ = lean_int_dec_lt(v_mantissa_3917_, v_intZero_3894_);
if (v_isNeg_3919_ == 0)
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_eq(v_exponent_3918_, v_natZero_3893_);
lean_dec(v_exponent_3918_);
if (v___x_3920_ == 0)
{
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3865_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3922_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3921_);
if (lean_obj_tag(v___x_3922_) == 1)
{
lean_object* v_val_3923_; 
v_val_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_val_3923_);
lean_dec_ref_known(v___x_3922_, 1);
if (lean_obj_tag(v_val_3923_) == 2)
{
lean_object* v_n_3924_; lean_object* v_mantissa_3925_; lean_object* v_exponent_3926_; uint8_t v_isNeg_3927_; 
v_n_3924_ = lean_ctor_get(v_val_3923_, 0);
lean_inc_ref(v_n_3924_);
lean_dec_ref_known(v_val_3923_, 1);
v_mantissa_3925_ = lean_ctor_get(v_n_3924_, 0);
lean_inc(v_mantissa_3925_);
v_exponent_3926_ = lean_ctor_get(v_n_3924_, 1);
lean_inc(v_exponent_3926_);
lean_dec_ref(v_n_3924_);
v_isNeg_3927_ = lean_int_dec_lt(v_mantissa_3925_, v_intZero_3894_);
if (v_isNeg_3927_ == 0)
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_nat_dec_eq(v_exponent_3926_, v_natZero_3893_);
lean_dec(v_exponent_3926_);
if (v___x_3928_ == 0)
{
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3868_;
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0));
v___x_3930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3929_);
if (lean_obj_tag(v___x_3930_) == 1)
{
lean_object* v_val_3931_; 
v_val_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v___x_3930_, 1);
if (lean_obj_tag(v_val_3931_) == 2)
{
lean_object* v_n_3932_; lean_object* v_mantissa_3933_; lean_object* v_exponent_3934_; uint8_t v_isNeg_3935_; 
v_n_3932_ = lean_ctor_get(v_val_3931_, 0);
lean_inc_ref(v_n_3932_);
lean_dec_ref_known(v_val_3931_, 1);
v_mantissa_3933_ = lean_ctor_get(v_n_3932_, 0);
lean_inc(v_mantissa_3933_);
v_exponent_3934_ = lean_ctor_get(v_n_3932_, 1);
lean_inc(v_exponent_3934_);
lean_dec_ref(v_n_3932_);
v_isNeg_3935_ = lean_int_dec_lt(v_mantissa_3933_, v_intZero_3894_);
if (v_isNeg_3935_ == 0)
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_nat_dec_eq(v_exponent_3934_, v_natZero_3893_);
lean_dec(v_exponent_3934_);
if (v___x_3936_ == 0)
{
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3871_;
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1));
v___x_3938_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3937_);
if (lean_obj_tag(v___x_3938_) == 1)
{
lean_object* v_val_3939_; 
v_val_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v___x_3938_, 1);
if (lean_obj_tag(v_val_3939_) == 2)
{
lean_object* v_n_3940_; lean_object* v_mantissa_3941_; lean_object* v_exponent_3942_; uint8_t v_isNeg_3943_; 
v_n_3940_ = lean_ctor_get(v_val_3939_, 0);
lean_inc_ref(v_n_3940_);
lean_dec_ref_known(v_val_3939_, 1);
v_mantissa_3941_ = lean_ctor_get(v_n_3940_, 0);
lean_inc(v_mantissa_3941_);
v_exponent_3942_ = lean_ctor_get(v_n_3940_, 1);
lean_inc(v_exponent_3942_);
lean_dec_ref(v_n_3940_);
v_isNeg_3943_ = lean_int_dec_lt(v_mantissa_3941_, v_intZero_3894_);
if (v_isNeg_3943_ == 0)
{
uint8_t v___x_3944_; 
v___x_3944_ = lean_nat_dec_eq(v_exponent_3942_, v_natZero_3893_);
lean_dec(v_exponent_3942_);
if (v___x_3944_ == 0)
{
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3874_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2));
v___x_3946_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3945_);
if (lean_obj_tag(v___x_3946_) == 1)
{
lean_object* v_val_3947_; 
v_val_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_val_3947_);
lean_dec_ref_known(v___x_3946_, 1);
if (lean_obj_tag(v_val_3947_) == 1)
{
uint8_t v_b_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_b_3948_ = lean_ctor_get_uint8(v_val_3947_, 0);
lean_dec_ref_known(v_val_3947_, 0);
v___x_3949_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3));
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3949_);
if (lean_obj_tag(v___x_3950_) == 1)
{
lean_object* v_val_3951_; 
v_val_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v___x_3950_, 1);
if (lean_obj_tag(v_val_3951_) == 4)
{
lean_object* v_elems_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4090_; 
v_elems_3952_ = lean_ctor_get(v_val_3951_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_val_3951_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_3954_ = v_val_3951_;
v_isShared_3955_ = v_isSharedCheck_4090_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_elems_3952_);
lean_dec(v_val_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4090_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3957_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3886_, v___x_3956_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4089_; 
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_4089_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4089_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
if (lean_obj_tag(v_val_3958_) == 1)
{
uint8_t v_b_3962_; lean_object* v_nameMap_3963_; lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_b_3962_ = lean_ctor_get_uint8(v_val_3958_, 0);
lean_dec_ref_known(v_val_3958_, 0);
v_nameMap_3963_ = lean_ctor_get(v_a_3851_, 1);
v_a_3964_ = lean_nat_abs(v_mantissa_3891_);
lean_dec(v_mantissa_3891_);
v___x_3965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3965_) == 1)
{
lean_object* v_val_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v_a_3964_);
lean_del_object(v___x_3960_);
lean_del_object(v___x_3954_);
v_val_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_4079_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_val_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4079_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; 
v___x_3970_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3900_, v_a_3851_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_4070_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_4070_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_4070_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v_snd_3975_; lean_object* v_fst_3976_; lean_object* v_exprMap_3977_; lean_object* v_a_3978_; lean_object* v___x_3979_; 
v_snd_3975_ = lean_ctor_get(v_a_3971_, 1);
lean_inc(v_snd_3975_);
v_fst_3976_ = lean_ctor_get(v_a_3971_, 0);
lean_inc(v_fst_3976_);
lean_dec(v_a_3971_);
v_exprMap_3977_ = lean_ctor_get(v_snd_3975_, 3);
v_a_3978_ = lean_nat_abs(v_mantissa_3905_);
lean_dec(v_mantissa_3905_);
v___x_3979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3977_, v_a_3978_);
if (lean_obj_tag(v___x_3979_) == 1)
{
lean_object* v_val_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4060_; 
lean_dec(v_a_3978_);
lean_del_object(v___x_3973_);
lean_del_object(v___x_3968_);
v_val_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_4060_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_val_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4060_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3912_, v_snd_3975_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v_fst_3986_; lean_object* v_snd_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v_fst_3986_ = lean_ctor_get(v_a_3985_, 0);
lean_inc(v_fst_3986_);
v_snd_3987_ = lean_ctor_get(v_a_3985_, 1);
lean_inc(v_snd_3987_);
lean_dec(v_a_3985_);
v___x_3988_ = lean_array_to_list(v_elems_3952_);
v___x_3989_ = lean_box(0);
v___x_3990_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v___x_3988_, v___x_3989_, v_snd_3987_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4043_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4043_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4043_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_snd_3995_; lean_object* v_fst_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4042_; 
v_snd_3995_ = lean_ctor_get(v_a_3991_, 1);
v_fst_3996_ = lean_ctor_get(v_a_3991_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_3991_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_3998_ = v_a_3991_;
v_isShared_3999_ = v_isSharedCheck_4042_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_snd_3995_);
lean_inc(v_fst_3996_);
lean_dec(v_a_3991_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4042_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v_stream_4000_; lean_object* v_nameMap_4001_; lean_object* v_levelMap_4002_; lean_object* v_exprMap_4003_; lean_object* v_recursorRuleMap_4004_; lean_object* v_constMap_4005_; lean_object* v_constOrder_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4041_; 
v_stream_4000_ = lean_ctor_get(v_snd_3995_, 0);
v_nameMap_4001_ = lean_ctor_get(v_snd_3995_, 1);
v_levelMap_4002_ = lean_ctor_get(v_snd_3995_, 2);
v_exprMap_4003_ = lean_ctor_get(v_snd_3995_, 3);
v_recursorRuleMap_4004_ = lean_ctor_get(v_snd_3995_, 4);
v_constMap_4005_ = lean_ctor_get(v_snd_3995_, 5);
v_constOrder_4006_ = lean_ctor_get(v_snd_3995_, 6);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_snd_3995_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4008_ = v_snd_3995_;
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_constOrder_4006_);
lean_inc(v_constMap_4005_);
lean_inc(v_recursorRuleMap_4004_);
lean_inc(v_exprMap_4003_);
lean_inc(v_levelMap_4002_);
lean_inc(v_nameMap_4001_);
lean_inc(v_stream_4000_);
lean_dec(v_snd_3995_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
uint8_t v___x_4010_; 
v___x_4010_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_4005_, v_val_3966_);
if (v___x_4010_ == 0)
{
lean_object* v_a_4011_; lean_object* v_a_4012_; lean_object* v_a_4013_; lean_object* v_a_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
v_a_4011_ = lean_nat_abs(v_mantissa_3917_);
lean_dec(v_mantissa_3917_);
v_a_4012_ = lean_nat_abs(v_mantissa_3925_);
lean_dec(v_mantissa_3925_);
v_a_4013_ = lean_nat_abs(v_mantissa_3933_);
lean_dec(v_mantissa_3933_);
v_a_4014_ = lean_nat_abs(v_mantissa_3941_);
lean_dec(v_mantissa_3941_);
lean_inc(v_val_3966_);
v___x_4015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4015_, 0, v_val_3966_);
lean_ctor_set(v___x_4015_, 1, v_fst_3976_);
lean_ctor_set(v___x_4015_, 2, v_val_3980_);
v___x_4016_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v_fst_3986_);
lean_ctor_set(v___x_4016_, 2, v_a_4011_);
lean_ctor_set(v___x_4016_, 3, v_a_4012_);
lean_ctor_set(v___x_4016_, 4, v_a_4013_);
lean_ctor_set(v___x_4016_, 5, v_a_4014_);
lean_ctor_set(v___x_4016_, 6, v_fst_3996_);
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*7, v_b_3948_);
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*7 + 1, v_b_3962_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set_tag(v___x_3982_, 7);
lean_ctor_set(v___x_3982_, 0, v___x_4016_);
v___x_4018_ = v___x_3982_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4019_ = lean_box(0);
lean_inc(v_val_3966_);
v___x_4020_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_4005_, v_val_3966_, v___x_4018_);
v___x_4021_ = lean_array_push(v_constOrder_4006_, v_val_3966_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 6, v___x_4021_);
lean_ctor_set(v___x_4008_, 5, v___x_4020_);
v___x_4023_ = v___x_4008_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_stream_4000_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_nameMap_4001_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_levelMap_4002_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_exprMap_4003_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_recursorRuleMap_4004_);
lean_ctor_set(v_reuseFailAlloc_4030_, 5, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4030_, 6, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4025_; 
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 1, v___x_4023_);
lean_ctor_set(v___x_3998_, 0, v___x_4019_);
v___x_4025_ = v___x_3998_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4027_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_4025_);
v___x_4027_ = v___x_3993_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
else
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
lean_del_object(v___x_4008_);
lean_dec_ref(v_constOrder_4006_);
lean_dec_ref(v_constMap_4005_);
lean_dec_ref(v_recursorRuleMap_4004_);
lean_dec_ref(v_exprMap_4003_);
lean_dec_ref(v_levelMap_4002_);
lean_dec_ref(v_nameMap_4001_);
lean_dec_ref(v_stream_4000_);
lean_del_object(v___x_3998_);
lean_dec(v_fst_3996_);
lean_dec(v_fst_3986_);
lean_dec(v_val_3980_);
lean_dec(v_fst_3976_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
v___x_4032_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_4033_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3966_, v___x_4010_);
v___x_4034_ = lean_string_append(v___x_4032_, v___x_4033_);
lean_dec_ref(v___x_4033_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set_tag(v___x_3982_, 18);
lean_ctor_set(v___x_3982_, 0, v___x_4034_);
v___x_4036_ = v___x_3982_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set_tag(v___x_3993_, 1);
lean_ctor_set(v___x_3993_, 0, v___x_4036_);
v___x_4038_ = v___x_3993_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_fst_3986_);
lean_del_object(v___x_3982_);
lean_dec(v_val_3980_);
lean_dec(v_fst_3976_);
lean_dec(v_val_3966_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
v_a_4044_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_3990_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_3990_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_del_object(v___x_3982_);
lean_dec(v_val_3980_);
lean_dec(v_fst_3976_);
lean_dec(v_val_3966_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
v_a_4052_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_3984_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_3984_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec(v___x_3979_);
lean_dec(v_fst_3976_);
lean_dec(v_snd_3975_);
lean_dec(v_val_3966_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
v___x_4061_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_4062_ = l_Nat_reprFast(v_a_3978_);
v___x_4063_ = lean_string_append(v___x_4061_, v___x_4062_);
lean_dec_ref(v___x_4062_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set_tag(v___x_3968_, 18);
lean_ctor_set(v___x_3968_, 0, v___x_4063_);
v___x_4065_ = v___x_3968_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4067_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set_tag(v___x_3973_, 1);
lean_ctor_set(v___x_3973_, 0, v___x_4065_);
v___x_4067_ = v___x_3973_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_del_object(v___x_3968_);
lean_dec(v_val_3966_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
v_a_4071_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_3970_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_3970_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
lean_dec(v___x_3965_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec_ref(v_a_3851_);
v___x_4080_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_4081_ = l_Nat_reprFast(v_a_3964_);
v___x_4082_ = lean_string_append(v___x_4080_, v___x_4081_);
lean_dec_ref(v___x_4081_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 18);
lean_ctor_set(v___x_3960_, 0, v___x_4082_);
v___x_4084_ = v___x_3960_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set_tag(v___x_3954_, 1);
lean_ctor_set(v___x_3954_, 0, v___x_4084_);
v___x_4086_ = v___x_3954_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3954_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3883_;
}
}
}
else
{
lean_dec(v___x_3957_);
lean_del_object(v___x_3954_);
lean_dec_ref(v_elems_3952_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3883_;
}
}
}
else
{
lean_dec(v_val_3951_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3880_;
}
}
else
{
lean_dec(v___x_3950_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3880_;
}
}
else
{
lean_dec(v_val_3947_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3877_;
}
}
else
{
lean_dec(v___x_3946_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3877_;
}
}
}
else
{
lean_dec(v_exponent_3942_);
lean_dec(v_mantissa_3941_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3874_;
}
}
else
{
lean_dec(v_val_3939_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3874_;
}
}
else
{
lean_dec(v___x_3938_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3874_;
}
}
}
else
{
lean_dec(v_exponent_3934_);
lean_dec(v_mantissa_3933_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3871_;
}
}
else
{
lean_dec(v_val_3931_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3871_;
}
}
else
{
lean_dec(v___x_3930_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3871_;
}
}
}
else
{
lean_dec(v_exponent_3926_);
lean_dec(v_mantissa_3925_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3868_;
}
}
else
{
lean_dec(v_val_3923_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3868_;
}
}
else
{
lean_dec(v___x_3922_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3868_;
}
}
}
else
{
lean_dec(v_exponent_3918_);
lean_dec(v_mantissa_3917_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3865_;
}
}
else
{
lean_dec(v_val_3915_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3865_;
}
}
else
{
lean_dec(v___x_3914_);
lean_dec_ref(v_elems_3912_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3865_;
}
}
else
{
lean_dec(v_val_3911_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3862_;
}
}
else
{
lean_dec(v___x_3910_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3862_;
}
}
}
else
{
lean_dec(v_exponent_3906_);
lean_dec(v_mantissa_3905_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3859_;
}
}
else
{
lean_dec(v_val_3903_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3859_;
}
}
else
{
lean_dec(v___x_3902_);
lean_dec_ref(v_elems_3900_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3859_;
}
}
else
{
lean_dec(v_val_3899_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3856_;
}
}
else
{
lean_dec(v___x_3898_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3856_;
}
}
}
else
{
lean_dec(v_exponent_3892_);
lean_dec(v_mantissa_3891_);
lean_dec_ref(v_a_3851_);
goto v___jp_3853_;
}
}
else
{
lean_dec(v_val_3889_);
lean_dec_ref(v_a_3851_);
goto v___jp_3853_;
}
}
else
{
lean_dec(v___x_3888_);
lean_dec_ref(v_a_3851_);
goto v___jp_3853_;
}
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_dec_ref(v_a_3851_);
v___x_4091_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
v___jp_3853_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
v___jp_3856_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
return v___x_3858_;
}
v___jp_3859_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
v___jp_3862_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
return v___x_3864_;
}
v___jp_3865_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
v___jp_3868_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
return v___x_3870_;
}
v___jp_3871_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
return v___x_3873_;
}
v___jp_3874_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
return v___x_3876_;
}
v___jp_3877_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
v___jp_3880_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
v___jp_3883_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___boxed(lean_object* v_json_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v_json_4093_, v_a_4094_);
lean_dec(v_json_4093_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(lean_object* v_as_4097_, size_t v_i_4098_, size_t v_stop_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_){
_start:
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_usize_dec_eq(v_i_4098_, v_stop_4099_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_array_uget_borrowed(v_as_4097_, v_i_4098_);
v___x_4105_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v___x_4104_, v___y_4101_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v_fst_4107_; lean_object* v_snd_4108_; size_t v___x_4109_; size_t v___x_4110_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v_fst_4107_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_fst_4107_);
v_snd_4108_ = lean_ctor_get(v_a_4106_, 1);
lean_inc(v_snd_4108_);
lean_dec(v_a_4106_);
v___x_4109_ = ((size_t)1ULL);
v___x_4110_ = lean_usize_add(v_i_4098_, v___x_4109_);
v_i_4098_ = v___x_4110_;
v_b_4100_ = v_fst_4107_;
v___y_4101_ = v_snd_4108_;
goto _start;
}
else
{
return v___x_4105_;
}
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_b_4100_);
lean_ctor_set(v___x_4112_, 1, v___y_4101_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0___boxed(lean_object* v_as_4114_, lean_object* v_i_4115_, lean_object* v_stop_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
size_t v_i_boxed_4120_; size_t v_stop_boxed_4121_; lean_object* v_res_4122_; 
v_i_boxed_4120_ = lean_unbox_usize(v_i_4115_);
lean_dec(v_i_4115_);
v_stop_boxed_4121_ = lean_unbox_usize(v_stop_4116_);
lean_dec(v_stop_4116_);
v_res_4122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_as_4114_, v_i_boxed_4120_, v_stop_boxed_4121_, v_b_4117_, v___y_4118_);
lean_dec_ref(v_as_4114_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(lean_object* v_as_4123_, size_t v_i_4124_, size_t v_stop_4125_, lean_object* v_b_4126_, lean_object* v___y_4127_){
_start:
{
uint8_t v___x_4129_; 
v___x_4129_ = lean_usize_dec_eq(v_i_4124_, v_stop_4125_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_array_uget_borrowed(v_as_4123_, v_i_4124_);
v___x_4131_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v___x_4130_, v___y_4127_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; size_t v___x_4135_; size_t v___x_4136_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v_fst_4133_ = lean_ctor_get(v_a_4132_, 0);
lean_inc(v_fst_4133_);
v_snd_4134_ = lean_ctor_get(v_a_4132_, 1);
lean_inc(v_snd_4134_);
lean_dec(v_a_4132_);
v___x_4135_ = ((size_t)1ULL);
v___x_4136_ = lean_usize_add(v_i_4124_, v___x_4135_);
v_i_4124_ = v___x_4136_;
v_b_4126_ = v_fst_4133_;
v___y_4127_ = v_snd_4134_;
goto _start;
}
else
{
return v___x_4131_;
}
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_b_4126_);
lean_ctor_set(v___x_4138_, 1, v___y_4127_);
v___x_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
return v___x_4139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1___boxed(lean_object* v_as_4140_, lean_object* v_i_4141_, lean_object* v_stop_4142_, lean_object* v_b_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_i_boxed_4146_; size_t v_stop_boxed_4147_; lean_object* v_res_4148_; 
v_i_boxed_4146_ = lean_unbox_usize(v_i_4141_);
lean_dec(v_i_4141_);
v_stop_boxed_4147_ = lean_unbox_usize(v_stop_4142_);
lean_dec(v_stop_4142_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_as_4140_, v_i_boxed_4146_, v_stop_boxed_4147_, v_b_4143_, v___y_4144_);
lean_dec_ref(v_as_4140_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(lean_object* v_as_4149_, size_t v_i_4150_, size_t v_stop_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_){
_start:
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_usize_dec_eq(v_i_4150_, v_stop_4151_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_array_uget_borrowed(v_as_4149_, v_i_4150_);
v___x_4157_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v___x_4156_, v___y_4153_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2___boxed(lean_object* v_as_4166_, lean_object* v_i_4167_, lean_object* v_stop_4168_, lean_object* v_b_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
size_t v_i_boxed_4172_; size_t v_stop_boxed_4173_; lean_object* v_res_4174_; 
v_i_boxed_4172_ = lean_unbox_usize(v_i_4167_);
lean_dec(v_i_4167_);
v_stop_boxed_4173_ = lean_unbox_usize(v_stop_4168_);
lean_dec(v_stop_4168_);
v_res_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_as_4166_, v_i_boxed_4172_, v_stop_boxed_4173_, v_b_4169_, v___y_4170_);
lean_dec_ref(v_as_4166_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(lean_object* v_data_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6));
v___x_4199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4186_, v___x_4198_);
if (lean_obj_tag(v___x_4199_) == 1)
{
lean_object* v_val_4200_; 
v_val_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_val_4200_);
lean_dec_ref_known(v___x_4199_, 1);
if (lean_obj_tag(v_val_4200_) == 4)
{
lean_object* v_elems_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_elems_4201_ = lean_ctor_get(v_val_4200_, 0);
lean_inc_ref(v_elems_4201_);
lean_dec_ref_known(v_val_4200_, 1);
v___x_4202_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_4203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4186_, v___x_4202_);
if (lean_obj_tag(v___x_4203_) == 1)
{
lean_object* v_val_4204_; 
v_val_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_val_4204_);
lean_dec_ref_known(v___x_4203_, 1);
if (lean_obj_tag(v_val_4204_) == 4)
{
lean_object* v_elems_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_elems_4205_ = lean_ctor_get(v_val_4204_, 0);
lean_inc_ref(v_elems_4205_);
lean_dec_ref_known(v_val_4204_, 1);
v___x_4206_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7));
v___x_4207_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4186_, v___x_4206_);
if (lean_obj_tag(v___x_4207_) == 1)
{
lean_object* v_val_4208_; 
v_val_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_val_4208_);
lean_dec_ref_known(v___x_4207_, 1);
if (lean_obj_tag(v_val_4208_) == 4)
{
lean_object* v_elems_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4264_; 
v_elems_4209_ = lean_ctor_get(v_val_4208_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_val_4208_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4211_ = v_val_4208_;
v_isShared_4212_ = v_isSharedCheck_4264_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_elems_4209_);
lean_dec(v_val_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4264_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v_snd_4215_; lean_object* v___y_4235_; lean_object* v_snd_4239_; lean_object* v___y_4251_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4254_ = lean_array_get_size(v_elems_4201_);
v___x_4255_ = lean_nat_dec_lt(v___x_4213_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_dec_ref(v_elems_4201_);
v_snd_4239_ = v_a_4187_;
goto v___jp_4238_;
}
else
{
lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4256_ = lean_box(0);
v___x_4257_ = lean_nat_dec_le(v___x_4254_, v___x_4254_);
if (v___x_4257_ == 0)
{
if (v___x_4255_ == 0)
{
lean_dec_ref(v_elems_4201_);
v_snd_4239_ = v_a_4187_;
goto v___jp_4238_;
}
else
{
size_t v___x_4258_; size_t v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = lean_usize_of_nat(v___x_4254_);
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4201_, v___x_4258_, v___x_4259_, v___x_4256_, v_a_4187_);
lean_dec_ref(v_elems_4201_);
v___y_4251_ = v___x_4260_;
goto v___jp_4250_;
}
}
else
{
size_t v___x_4261_; size_t v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = ((size_t)0ULL);
v___x_4262_ = lean_usize_of_nat(v___x_4254_);
v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4201_, v___x_4261_, v___x_4262_, v___x_4256_, v_a_4187_);
lean_dec_ref(v_elems_4201_);
v___y_4251_ = v___x_4263_;
goto v___jp_4250_;
}
}
v___jp_4214_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_array_get_size(v_elems_4209_);
v___x_4217_ = lean_box(0);
v___x_4218_ = lean_nat_dec_lt(v___x_4213_, v___x_4216_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_dec_ref(v_elems_4209_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v_snd_4215_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4219_);
v___x_4221_ = v___x_4211_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
else
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_nat_dec_le(v___x_4216_, v___x_4216_);
if (v___x_4223_ == 0)
{
if (v___x_4218_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
lean_dec_ref(v_elems_4209_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4217_);
lean_ctor_set(v___x_4224_, 1, v_snd_4215_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4224_);
v___x_4226_ = v___x_4211_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
else
{
size_t v___x_4228_; size_t v___x_4229_; lean_object* v___x_4230_; 
lean_del_object(v___x_4211_);
v___x_4228_ = ((size_t)0ULL);
v___x_4229_ = lean_usize_of_nat(v___x_4216_);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4209_, v___x_4228_, v___x_4229_, v___x_4217_, v_snd_4215_);
lean_dec_ref(v_elems_4209_);
return v___x_4230_;
}
}
else
{
size_t v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
lean_del_object(v___x_4211_);
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = lean_usize_of_nat(v___x_4216_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4209_, v___x_4231_, v___x_4232_, v___x_4217_, v_snd_4215_);
lean_dec_ref(v_elems_4209_);
return v___x_4233_;
}
}
}
v___jp_4234_:
{
if (lean_obj_tag(v___y_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v_snd_4237_; 
v_a_4236_ = lean_ctor_get(v___y_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___y_4235_, 1);
v_snd_4237_ = lean_ctor_get(v_a_4236_, 1);
lean_inc(v_snd_4237_);
lean_dec(v_a_4236_);
v_snd_4215_ = v_snd_4237_;
goto v___jp_4214_;
}
else
{
lean_del_object(v___x_4211_);
lean_dec_ref(v_elems_4209_);
return v___y_4235_;
}
}
v___jp_4238_:
{
lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4240_ = lean_array_get_size(v_elems_4205_);
v___x_4241_ = lean_nat_dec_lt(v___x_4213_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_dec_ref(v_elems_4205_);
v_snd_4215_ = v_snd_4239_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_nat_dec_le(v___x_4240_, v___x_4240_);
if (v___x_4243_ == 0)
{
if (v___x_4241_ == 0)
{
lean_dec_ref(v_elems_4205_);
v_snd_4215_ = v_snd_4239_;
goto v___jp_4214_;
}
else
{
size_t v___x_4244_; size_t v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = ((size_t)0ULL);
v___x_4245_ = lean_usize_of_nat(v___x_4240_);
v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4205_, v___x_4244_, v___x_4245_, v___x_4242_, v_snd_4239_);
lean_dec_ref(v_elems_4205_);
v___y_4235_ = v___x_4246_;
goto v___jp_4234_;
}
}
else
{
size_t v___x_4247_; size_t v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = ((size_t)0ULL);
v___x_4248_ = lean_usize_of_nat(v___x_4240_);
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4205_, v___x_4247_, v___x_4248_, v___x_4242_, v_snd_4239_);
lean_dec_ref(v_elems_4205_);
v___y_4235_ = v___x_4249_;
goto v___jp_4234_;
}
}
}
v___jp_4250_:
{
if (lean_obj_tag(v___y_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v_snd_4253_; 
v_a_4252_ = lean_ctor_get(v___y_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___y_4251_, 1);
v_snd_4253_ = lean_ctor_get(v_a_4252_, 1);
lean_inc(v_snd_4253_);
lean_dec(v_a_4252_);
v_snd_4239_ = v_snd_4253_;
goto v___jp_4238_;
}
else
{
lean_del_object(v___x_4211_);
lean_dec_ref(v_elems_4209_);
lean_dec_ref(v_elems_4205_);
return v___y_4251_;
}
}
}
}
else
{
lean_dec(v_val_4208_);
lean_dec_ref(v_elems_4205_);
lean_dec_ref(v_elems_4201_);
lean_dec_ref(v_a_4187_);
goto v___jp_4189_;
}
}
else
{
lean_dec(v___x_4207_);
lean_dec_ref(v_elems_4205_);
lean_dec_ref(v_elems_4201_);
lean_dec_ref(v_a_4187_);
goto v___jp_4189_;
}
}
else
{
lean_dec(v_val_4204_);
lean_dec_ref(v_elems_4201_);
lean_dec_ref(v_a_4187_);
goto v___jp_4192_;
}
}
else
{
lean_dec(v___x_4203_);
lean_dec_ref(v_elems_4201_);
lean_dec_ref(v_a_4187_);
goto v___jp_4192_;
}
}
else
{
lean_dec(v_val_4200_);
lean_dec_ref(v_a_4187_);
goto v___jp_4195_;
}
}
else
{
lean_dec(v___x_4199_);
lean_dec_ref(v_a_4187_);
goto v___jp_4195_;
}
v___jp_4189_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1));
v___x_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
v___jp_4192_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3));
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
v___jp_4195_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5));
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___boxed(lean_object* v_data_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_data_4265_, v_a_4266_);
lean_dec(v_data_4265_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(lean_object* v_x_4270_, lean_object* v_x_4271_){
_start:
{
if (lean_obj_tag(v_x_4271_) == 0)
{
return v_x_4270_;
}
else
{
lean_object* v_head_4272_; lean_object* v_tail_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_head_4272_ = lean_ctor_get(v_x_4271_, 0);
v_tail_4273_ = lean_ctor_get(v_x_4271_, 1);
v___x_4274_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0));
v___x_4275_ = lean_string_append(v_x_4270_, v___x_4274_);
v___x_4276_ = lean_string_append(v___x_4275_, v_head_4272_);
v_x_4270_ = v___x_4276_;
v_x_4271_ = v_tail_4273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___boxed(lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v_x_4278_, v_x_4279_);
lean_dec(v_x_4279_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v___x_4285_; 
v___x_4285_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0));
return v___x_4285_;
}
else
{
lean_object* v_tail_4286_; 
v_tail_4286_ = lean_ctor_get(v_x_4284_, 1);
if (lean_obj_tag(v_tail_4286_) == 0)
{
lean_object* v_head_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_head_4287_ = lean_ctor_get(v_x_4284_, 0);
v___x_4288_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4289_ = lean_string_append(v___x_4288_, v_head_4287_);
v___x_4290_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2));
v___x_4291_ = lean_string_append(v___x_4289_, v___x_4290_);
return v___x_4291_;
}
else
{
lean_object* v_head_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint32_t v___x_4296_; lean_object* v___x_4297_; 
v_head_4292_ = lean_ctor_get(v_x_4284_, 0);
v___x_4293_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4294_ = lean_string_append(v___x_4293_, v_head_4292_);
v___x_4295_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v___x_4294_, v_tail_4286_);
v___x_4296_ = 93;
v___x_4297_ = lean_string_push(v___x_4295_, v___x_4296_);
return v___x_4297_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___boxed(lean_object* v_x_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_x_4298_);
lean_dec(v_x_4298_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object* v_init_4300_, lean_object* v_x_4301_){
_start:
{
if (lean_obj_tag(v_x_4301_) == 0)
{
lean_object* v_k_4302_; lean_object* v_v_4303_; lean_object* v_l_4304_; lean_object* v_r_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_k_4302_ = lean_ctor_get(v_x_4301_, 1);
v_v_4303_ = lean_ctor_get(v_x_4301_, 2);
v_l_4304_ = lean_ctor_get(v_x_4301_, 3);
v_r_4305_ = lean_ctor_get(v_x_4301_, 4);
v___x_4306_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_init_4300_, v_r_4305_);
lean_inc(v_v_4303_);
lean_inc(v_k_4302_);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_k_4302_);
lean_ctor_set(v___x_4307_, 1, v_v_4303_);
v___x_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_4306_);
v_init_4300_ = v___x_4308_;
v_x_4301_ = v_l_4304_;
goto _start;
}
else
{
return v_init_4300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object* v_init_4310_, lean_object* v_x_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_init_4310_, v_x_4311_);
lean_dec(v_x_4311_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(lean_object* v_init_4313_, lean_object* v_x_4314_){
_start:
{
if (lean_obj_tag(v_x_4314_) == 0)
{
lean_object* v_k_4315_; lean_object* v_l_4316_; lean_object* v_r_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_k_4315_ = lean_ctor_get(v_x_4314_, 1);
v_l_4316_ = lean_ctor_get(v_x_4314_, 3);
v_r_4317_ = lean_ctor_get(v_x_4314_, 4);
v___x_4318_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4313_, v_r_4317_);
lean_inc(v_k_4315_);
v___x_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4319_, 0, v_k_4315_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v_init_4313_ = v___x_4319_;
v_x_4314_ = v_l_4316_;
goto _start;
}
else
{
return v_init_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0___boxed(lean_object* v_init_4321_, lean_object* v_x_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4321_, v_x_4322_);
lean_dec(v_x_4322_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(lean_object* v_line_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
v___x_4356_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_4355_, v_line_4349_);
if (lean_obj_tag(v___x_4356_) == 1)
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_5230_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_5230_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_5230_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
if (lean_obj_tag(v_a_4357_) == 5)
{
lean_object* v_kvPairs_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_5229_; 
v_kvPairs_4361_ = lean_ctor_get(v_a_4357_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_a_4357_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_4363_ = v_a_4357_;
v_isShared_4364_ = v_isSharedCheck_5229_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_kvPairs_4361_);
lean_dec(v_a_4357_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_5229_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v_fst_4378_; lean_object* v_snd_4379_; lean_object* v_tail_4380_; lean_object* v___y_5196_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = lean_box(0);
v___x_5202_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v___x_5201_, v_kvPairs_4361_);
if (lean_obj_tag(v___x_5202_) == 1)
{
lean_object* v_tail_5203_; 
v_tail_5203_ = lean_ctor_get(v___x_5202_, 1);
lean_inc(v_tail_5203_);
if (lean_obj_tag(v_tail_5203_) == 1)
{
lean_object* v_head_5204_; lean_object* v_head_5205_; lean_object* v_tail_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5227_; 
v_head_5204_ = lean_ctor_get(v_tail_5203_, 0);
lean_inc(v_head_5204_);
v_head_5205_ = lean_ctor_get(v___x_5202_, 0);
lean_inc(v_head_5205_);
v_tail_5206_ = lean_ctor_get(v_tail_5203_, 1);
v_isSharedCheck_5227_ = !lean_is_exclusive(v_tail_5203_);
if (v_isSharedCheck_5227_ == 0)
{
lean_object* v_unused_5228_; 
v_unused_5228_ = lean_ctor_get(v_tail_5203_, 0);
lean_dec(v_unused_5228_);
v___x_5208_ = v_tail_5203_;
v_isShared_5209_ = v_isSharedCheck_5227_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_tail_5206_);
lean_dec(v_tail_5203_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5227_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v_fst_5210_; lean_object* v_snd_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
v_fst_5210_ = lean_ctor_get(v_head_5204_, 0);
lean_inc(v_fst_5210_);
v_snd_5211_ = lean_ctor_get(v_head_5204_, 1);
lean_inc(v_snd_5211_);
lean_dec(v_head_5204_);
v___x_5212_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_5213_ = lean_string_dec_eq(v_fst_5210_, v___x_5212_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5214_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_5215_ = lean_string_dec_eq(v_fst_5210_, v___x_5214_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5216_; uint8_t v___x_5217_; 
v___x_5216_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_5217_ = lean_string_dec_eq(v_fst_5210_, v___x_5216_);
lean_dec(v_fst_5210_);
if (v___x_5217_ == 0)
{
lean_dec(v_snd_5211_);
lean_del_object(v___x_5208_);
lean_dec(v_tail_5206_);
lean_dec(v_head_5205_);
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
else
{
if (lean_obj_tag(v_tail_5206_) == 0)
{
lean_object* v___x_5219_; 
lean_dec_ref_known(v___x_5202_, 2);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 0, v_head_5205_);
v___x_5219_ = v___x_5208_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_head_5205_);
lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_tail_5206_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
v_fst_4378_ = v___x_5216_;
v_snd_4379_ = v_snd_5211_;
v_tail_4380_ = v___x_5219_;
goto v___jp_4377_;
}
}
else
{
lean_dec(v_snd_5211_);
lean_del_object(v___x_5208_);
lean_dec(v_tail_5206_);
lean_dec(v_head_5205_);
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
}
}
else
{
lean_dec(v_fst_5210_);
if (lean_obj_tag(v_tail_5206_) == 0)
{
lean_object* v___x_5222_; 
lean_dec_ref_known(v___x_5202_, 2);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 0, v_head_5205_);
v___x_5222_ = v___x_5208_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_head_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_tail_5206_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
v_fst_4378_ = v___x_5214_;
v_snd_4379_ = v_snd_5211_;
v_tail_4380_ = v___x_5222_;
goto v___jp_4377_;
}
}
else
{
lean_dec(v_snd_5211_);
lean_del_object(v___x_5208_);
lean_dec(v_tail_5206_);
lean_dec(v_head_5205_);
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
}
}
else
{
lean_dec(v_fst_5210_);
if (lean_obj_tag(v_tail_5206_) == 0)
{
lean_object* v___x_5225_; 
lean_dec_ref_known(v___x_5202_, 2);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 0, v_head_5205_);
v___x_5225_ = v___x_5208_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_head_5205_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_tail_5206_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
v_fst_4378_ = v___x_5212_;
v_snd_4379_ = v_snd_5211_;
v_tail_4380_ = v___x_5225_;
goto v___jp_4377_;
}
}
else
{
lean_dec(v_snd_5211_);
lean_del_object(v___x_5208_);
lean_dec(v_tail_5206_);
lean_dec(v_head_5205_);
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
}
}
}
else
{
lean_dec(v_tail_5203_);
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
}
else
{
v___y_5196_ = v___x_5202_;
goto v___jp_5195_;
}
v___jp_4365_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
v___x_4366_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0));
v___x_4367_ = lean_box(0);
v___x_4368_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v___x_4367_, v_kvPairs_4361_);
lean_dec(v_kvPairs_4361_);
v___x_4369_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v___x_4368_);
lean_dec(v___x_4368_);
v___x_4370_ = lean_string_append(v___x_4366_, v___x_4369_);
lean_dec_ref(v___x_4369_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set_tag(v___x_4363_, 18);
lean_ctor_set(v___x_4363_, 0, v___x_4370_);
v___x_4372_ = v___x_4363_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 0, v___x_4372_);
v___x_4374_ = v___x_4359_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
v___jp_4377_:
{
lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_4382_ = lean_string_dec_eq(v_fst_4378_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_4384_ = lean_string_dec_eq(v_fst_4378_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4385_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_4386_ = lean_string_dec_eq(v_fst_4378_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4));
v___x_4388_ = lean_string_dec_eq(v_fst_4378_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5));
v___x_4390_ = lean_string_dec_eq(v_fst_4378_, v___x_4389_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4391_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6));
v___x_4392_ = lean_string_dec_eq(v_fst_4378_, v___x_4391_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4393_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_4394_ = lean_string_dec_eq(v_fst_4378_, v___x_4393_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7));
v___x_4396_ = lean_string_dec_eq(v_fst_4378_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4397_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8));
v___x_4398_ = lean_string_dec_eq(v_fst_4378_, v___x_4397_);
lean_dec_ref(v_fst_4378_);
if (v___x_4398_ == 0)
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4399_; lean_object* v___x_4400_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4399_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4399_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4400_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_kvPairs_4399_, v_a_4350_);
lean_dec(v_kvPairs_4399_);
return v___x_4400_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4401_; lean_object* v___x_4402_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4401_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4401_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4402_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_kvPairs_4401_, v_a_4350_);
lean_dec(v_kvPairs_4401_);
return v___x_4402_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4403_; lean_object* v___x_4404_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4403_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4403_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4404_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_kvPairs_4403_, v_a_4350_);
lean_dec(v_kvPairs_4403_);
return v___x_4404_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4405_; lean_object* v___x_4406_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4405_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4405_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4406_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_kvPairs_4405_, v_a_4350_);
lean_dec(v_kvPairs_4405_);
return v___x_4406_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4407_; lean_object* v___x_4408_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4407_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4407_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4408_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_kvPairs_4407_, v_a_4350_);
lean_dec(v_kvPairs_4407_);
return v___x_4408_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 5)
{
if (lean_obj_tag(v_tail_4380_) == 0)
{
lean_object* v_kvPairs_4409_; lean_object* v___x_4410_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v_kvPairs_4409_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_kvPairs_4409_);
lean_dec_ref_known(v_snd_4379_, 1);
v___x_4410_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_kvPairs_4409_, v_a_4350_);
lean_dec(v_kvPairs_4409_);
return v___x_4410_;
}
else
{
lean_dec_ref_known(v_snd_4379_, 1);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 2)
{
lean_object* v_n_4411_; lean_object* v_mantissa_4412_; lean_object* v_exponent_4413_; lean_object* v_natZero_4414_; lean_object* v_intZero_4415_; uint8_t v_isNeg_4416_; 
v_n_4411_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc_ref(v_n_4411_);
lean_dec_ref_known(v_snd_4379_, 1);
v_mantissa_4412_ = lean_ctor_get(v_n_4411_, 0);
lean_inc(v_mantissa_4412_);
v_exponent_4413_ = lean_ctor_get(v_n_4411_, 1);
lean_inc(v_exponent_4413_);
lean_dec_ref(v_n_4411_);
v_natZero_4414_ = lean_unsigned_to_nat(0u);
v_intZero_4415_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4416_ = lean_int_dec_lt(v_mantissa_4412_, v_intZero_4415_);
if (v_isNeg_4416_ == 0)
{
uint8_t v___x_4417_; 
v___x_4417_ = lean_nat_dec_eq(v_exponent_4413_, v_natZero_4414_);
lean_dec(v_exponent_4413_);
if (v___x_4417_ == 0)
{
lean_dec(v_mantissa_4412_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_4380_) == 1)
{
lean_object* v_head_4418_; lean_object* v_tail_4419_; lean_object* v_fst_4420_; lean_object* v_snd_4421_; lean_object* v_a_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v_head_4418_ = lean_ctor_get(v_tail_4380_, 0);
lean_inc(v_head_4418_);
v_tail_4419_ = lean_ctor_get(v_tail_4380_, 1);
lean_inc(v_tail_4419_);
lean_dec_ref_known(v_tail_4380_, 2);
v_fst_4420_ = lean_ctor_get(v_head_4418_, 0);
lean_inc(v_fst_4420_);
v_snd_4421_ = lean_ctor_get(v_head_4418_, 1);
lean_inc(v_snd_4421_);
lean_dec(v_head_4418_);
v_a_4422_ = lean_nat_abs(v_mantissa_4412_);
lean_dec(v_mantissa_4412_);
v___x_4423_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9));
v___x_4424_ = lean_string_dec_eq(v_fst_4420_, v___x_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4425_; uint8_t v___x_4426_; 
v___x_4425_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10));
v___x_4426_ = lean_string_dec_eq(v_fst_4420_, v___x_4425_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11));
v___x_4428_ = lean_string_dec_eq(v_fst_4420_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; uint8_t v___x_4430_; 
v___x_4429_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12));
v___x_4430_ = lean_string_dec_eq(v_fst_4420_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13));
v___x_4432_ = lean_string_dec_eq(v_fst_4420_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14));
v___x_4434_ = lean_string_dec_eq(v_fst_4420_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4435_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15));
v___x_4436_ = lean_string_dec_eq(v_fst_4420_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16));
v___x_4438_ = lean_string_dec_eq(v_fst_4420_, v___x_4437_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; uint8_t v___x_4440_; 
v___x_4439_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17));
v___x_4440_ = lean_string_dec_eq(v_fst_4420_, v___x_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4441_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18));
v___x_4442_ = lean_string_dec_eq(v_fst_4420_, v___x_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4443_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19));
v___x_4444_ = lean_string_dec_eq(v_fst_4420_, v___x_4443_);
lean_dec(v_fst_4420_);
if (v___x_4444_ == 0)
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4445_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4445_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4478_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4478_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4478_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v_snd_4450_; lean_object* v_fst_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4477_; 
v_snd_4450_ = lean_ctor_get(v_a_4446_, 1);
v_fst_4451_ = lean_ctor_get(v_a_4446_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_a_4446_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4453_ = v_a_4446_;
v_isShared_4454_ = v_isSharedCheck_4477_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_snd_4450_);
lean_inc(v_fst_4451_);
lean_dec(v_a_4446_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4477_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v_stream_4455_; lean_object* v_nameMap_4456_; lean_object* v_levelMap_4457_; lean_object* v_exprMap_4458_; lean_object* v_recursorRuleMap_4459_; lean_object* v_constMap_4460_; lean_object* v_constOrder_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4476_; 
v_stream_4455_ = lean_ctor_get(v_snd_4450_, 0);
v_nameMap_4456_ = lean_ctor_get(v_snd_4450_, 1);
v_levelMap_4457_ = lean_ctor_get(v_snd_4450_, 2);
v_exprMap_4458_ = lean_ctor_get(v_snd_4450_, 3);
v_recursorRuleMap_4459_ = lean_ctor_get(v_snd_4450_, 4);
v_constMap_4460_ = lean_ctor_get(v_snd_4450_, 5);
v_constOrder_4461_ = lean_ctor_get(v_snd_4450_, 6);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_snd_4450_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4463_ = v_snd_4450_;
v_isShared_4464_ = v_isSharedCheck_4476_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_constOrder_4461_);
lean_inc(v_constMap_4460_);
lean_inc(v_recursorRuleMap_4459_);
lean_inc(v_exprMap_4458_);
lean_inc(v_levelMap_4457_);
lean_inc(v_nameMap_4456_);
lean_inc(v_stream_4455_);
lean_dec(v_snd_4450_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4476_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4465_ = lean_box(0);
v___x_4466_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4458_, v_a_4422_, v_fst_4451_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 3, v___x_4466_);
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_stream_4455_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_nameMap_4456_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_levelMap_4457_);
lean_ctor_set(v_reuseFailAlloc_4475_, 3, v___x_4466_);
lean_ctor_set(v_reuseFailAlloc_4475_, 4, v_recursorRuleMap_4459_);
lean_ctor_set(v_reuseFailAlloc_4475_, 5, v_constMap_4460_);
lean_ctor_set(v_reuseFailAlloc_4475_, 6, v_constOrder_4461_);
v___x_4468_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 1, v___x_4468_);
lean_ctor_set(v___x_4453_, 0, v___x_4465_);
v___x_4470_ = v___x_4453_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4472_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4470_);
v___x_4472_ = v___x_4448_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
lean_dec(v_a_4422_);
v_a_4479_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4445_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4445_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4487_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4487_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_snd_4421_, v_a_4350_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4520_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4520_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4520_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_snd_4492_; lean_object* v_fst_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4519_; 
v_snd_4492_ = lean_ctor_get(v_a_4488_, 1);
v_fst_4493_ = lean_ctor_get(v_a_4488_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_a_4488_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4495_ = v_a_4488_;
v_isShared_4496_ = v_isSharedCheck_4519_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_snd_4492_);
lean_inc(v_fst_4493_);
lean_dec(v_a_4488_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4519_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_stream_4497_; lean_object* v_nameMap_4498_; lean_object* v_levelMap_4499_; lean_object* v_exprMap_4500_; lean_object* v_recursorRuleMap_4501_; lean_object* v_constMap_4502_; lean_object* v_constOrder_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4518_; 
v_stream_4497_ = lean_ctor_get(v_snd_4492_, 0);
v_nameMap_4498_ = lean_ctor_get(v_snd_4492_, 1);
v_levelMap_4499_ = lean_ctor_get(v_snd_4492_, 2);
v_exprMap_4500_ = lean_ctor_get(v_snd_4492_, 3);
v_recursorRuleMap_4501_ = lean_ctor_get(v_snd_4492_, 4);
v_constMap_4502_ = lean_ctor_get(v_snd_4492_, 5);
v_constOrder_4503_ = lean_ctor_get(v_snd_4492_, 6);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_snd_4492_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4505_ = v_snd_4492_;
v_isShared_4506_ = v_isSharedCheck_4518_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_constOrder_4503_);
lean_inc(v_constMap_4502_);
lean_inc(v_recursorRuleMap_4501_);
lean_inc(v_exprMap_4500_);
lean_inc(v_levelMap_4499_);
lean_inc(v_nameMap_4498_);
lean_inc(v_stream_4497_);
lean_dec(v_snd_4492_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4518_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4507_ = lean_box(0);
v___x_4508_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4500_, v_a_4422_, v_fst_4493_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 3, v___x_4508_);
v___x_4510_ = v___x_4505_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_stream_4497_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_nameMap_4498_);
lean_ctor_set(v_reuseFailAlloc_4517_, 2, v_levelMap_4499_);
lean_ctor_set(v_reuseFailAlloc_4517_, 3, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4517_, 4, v_recursorRuleMap_4501_);
lean_ctor_set(v_reuseFailAlloc_4517_, 5, v_constMap_4502_);
lean_ctor_set(v_reuseFailAlloc_4517_, 6, v_constOrder_4503_);
v___x_4510_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 1, v___x_4510_);
lean_ctor_set(v___x_4495_, 0, v___x_4507_);
v___x_4512_ = v___x_4495_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4514_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4512_);
v___x_4514_ = v___x_4490_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_a_4422_);
v_a_4521_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4487_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4487_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4529_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4529_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_snd_4421_, v_a_4350_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4562_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4562_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4562_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_snd_4534_; lean_object* v_fst_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4561_; 
v_snd_4534_ = lean_ctor_get(v_a_4530_, 1);
v_fst_4535_ = lean_ctor_get(v_a_4530_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_a_4530_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4537_ = v_a_4530_;
v_isShared_4538_ = v_isSharedCheck_4561_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_snd_4534_);
lean_inc(v_fst_4535_);
lean_dec(v_a_4530_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4561_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v_stream_4539_; lean_object* v_nameMap_4540_; lean_object* v_levelMap_4541_; lean_object* v_exprMap_4542_; lean_object* v_recursorRuleMap_4543_; lean_object* v_constMap_4544_; lean_object* v_constOrder_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4560_; 
v_stream_4539_ = lean_ctor_get(v_snd_4534_, 0);
v_nameMap_4540_ = lean_ctor_get(v_snd_4534_, 1);
v_levelMap_4541_ = lean_ctor_get(v_snd_4534_, 2);
v_exprMap_4542_ = lean_ctor_get(v_snd_4534_, 3);
v_recursorRuleMap_4543_ = lean_ctor_get(v_snd_4534_, 4);
v_constMap_4544_ = lean_ctor_get(v_snd_4534_, 5);
v_constOrder_4545_ = lean_ctor_get(v_snd_4534_, 6);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_snd_4534_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4547_ = v_snd_4534_;
v_isShared_4548_ = v_isSharedCheck_4560_;
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
v_isShared_4548_ = v_isSharedCheck_4560_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
v___x_4549_ = lean_box(0);
v___x_4550_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4542_, v_a_4422_, v_fst_4535_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 3, v___x_4550_);
v___x_4552_ = v___x_4547_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_stream_4539_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_nameMap_4540_);
lean_ctor_set(v_reuseFailAlloc_4559_, 2, v_levelMap_4541_);
lean_ctor_set(v_reuseFailAlloc_4559_, 3, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4559_, 4, v_recursorRuleMap_4543_);
lean_ctor_set(v_reuseFailAlloc_4559_, 5, v_constMap_4544_);
lean_ctor_set(v_reuseFailAlloc_4559_, 6, v_constOrder_4545_);
v___x_4552_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4554_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 1, v___x_4552_);
lean_ctor_set(v___x_4537_, 0, v___x_4549_);
v___x_4554_ = v___x_4537_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4556_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4554_);
v___x_4556_ = v___x_4532_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4422_);
v_a_4563_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4529_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4529_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4571_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4571_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4604_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4604_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4604_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v_snd_4576_; lean_object* v_fst_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4603_; 
v_snd_4576_ = lean_ctor_get(v_a_4572_, 1);
v_fst_4577_ = lean_ctor_get(v_a_4572_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_a_4572_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4579_ = v_a_4572_;
v_isShared_4580_ = v_isSharedCheck_4603_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_snd_4576_);
lean_inc(v_fst_4577_);
lean_dec(v_a_4572_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4603_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v_stream_4581_; lean_object* v_nameMap_4582_; lean_object* v_levelMap_4583_; lean_object* v_exprMap_4584_; lean_object* v_recursorRuleMap_4585_; lean_object* v_constMap_4586_; lean_object* v_constOrder_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4602_; 
v_stream_4581_ = lean_ctor_get(v_snd_4576_, 0);
v_nameMap_4582_ = lean_ctor_get(v_snd_4576_, 1);
v_levelMap_4583_ = lean_ctor_get(v_snd_4576_, 2);
v_exprMap_4584_ = lean_ctor_get(v_snd_4576_, 3);
v_recursorRuleMap_4585_ = lean_ctor_get(v_snd_4576_, 4);
v_constMap_4586_ = lean_ctor_get(v_snd_4576_, 5);
v_constOrder_4587_ = lean_ctor_get(v_snd_4576_, 6);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_snd_4576_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4589_ = v_snd_4576_;
v_isShared_4590_ = v_isSharedCheck_4602_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_constOrder_4587_);
lean_inc(v_constMap_4586_);
lean_inc(v_recursorRuleMap_4585_);
lean_inc(v_exprMap_4584_);
lean_inc(v_levelMap_4583_);
lean_inc(v_nameMap_4582_);
lean_inc(v_stream_4581_);
lean_dec(v_snd_4576_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4602_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4591_ = lean_box(0);
v___x_4592_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4584_, v_a_4422_, v_fst_4577_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 3, v___x_4592_);
v___x_4594_ = v___x_4589_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_stream_4581_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_nameMap_4582_);
lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_levelMap_4583_);
lean_ctor_set(v_reuseFailAlloc_4601_, 3, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4601_, 4, v_recursorRuleMap_4585_);
lean_ctor_set(v_reuseFailAlloc_4601_, 5, v_constMap_4586_);
lean_ctor_set(v_reuseFailAlloc_4601_, 6, v_constOrder_4587_);
v___x_4594_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4596_; 
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 1, v___x_4594_);
lean_ctor_set(v___x_4579_, 0, v___x_4591_);
v___x_4596_ = v___x_4579_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4598_; 
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4596_);
v___x_4598_ = v___x_4574_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec(v_a_4422_);
v_a_4605_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4571_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4571_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4613_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4613_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4646_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4646_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4646_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v_snd_4618_; lean_object* v_fst_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4645_; 
v_snd_4618_ = lean_ctor_get(v_a_4614_, 1);
v_fst_4619_ = lean_ctor_get(v_a_4614_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_a_4614_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4621_ = v_a_4614_;
v_isShared_4622_ = v_isSharedCheck_4645_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_snd_4618_);
lean_inc(v_fst_4619_);
lean_dec(v_a_4614_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4645_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v_stream_4623_; lean_object* v_nameMap_4624_; lean_object* v_levelMap_4625_; lean_object* v_exprMap_4626_; lean_object* v_recursorRuleMap_4627_; lean_object* v_constMap_4628_; lean_object* v_constOrder_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4644_; 
v_stream_4623_ = lean_ctor_get(v_snd_4618_, 0);
v_nameMap_4624_ = lean_ctor_get(v_snd_4618_, 1);
v_levelMap_4625_ = lean_ctor_get(v_snd_4618_, 2);
v_exprMap_4626_ = lean_ctor_get(v_snd_4618_, 3);
v_recursorRuleMap_4627_ = lean_ctor_get(v_snd_4618_, 4);
v_constMap_4628_ = lean_ctor_get(v_snd_4618_, 5);
v_constOrder_4629_ = lean_ctor_get(v_snd_4618_, 6);
v_isSharedCheck_4644_ = !lean_is_exclusive(v_snd_4618_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4631_ = v_snd_4618_;
v_isShared_4632_ = v_isSharedCheck_4644_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_constOrder_4629_);
lean_inc(v_constMap_4628_);
lean_inc(v_recursorRuleMap_4627_);
lean_inc(v_exprMap_4626_);
lean_inc(v_levelMap_4625_);
lean_inc(v_nameMap_4624_);
lean_inc(v_stream_4623_);
lean_dec(v_snd_4618_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4644_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4633_ = lean_box(0);
v___x_4634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4626_, v_a_4422_, v_fst_4619_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 3, v___x_4634_);
v___x_4636_ = v___x_4631_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_stream_4623_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_nameMap_4624_);
lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_levelMap_4625_);
lean_ctor_set(v_reuseFailAlloc_4643_, 3, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4643_, 4, v_recursorRuleMap_4627_);
lean_ctor_set(v_reuseFailAlloc_4643_, 5, v_constMap_4628_);
lean_ctor_set(v_reuseFailAlloc_4643_, 6, v_constOrder_4629_);
v___x_4636_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4638_; 
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 1, v___x_4636_);
lean_ctor_set(v___x_4621_, 0, v___x_4633_);
v___x_4638_ = v___x_4621_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
lean_object* v___x_4640_; 
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4638_);
v___x_4640_ = v___x_4616_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_a_4422_);
v_a_4647_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4613_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4613_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4655_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4655_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4688_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4688_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4688_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v_snd_4660_; lean_object* v_fst_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4687_; 
v_snd_4660_ = lean_ctor_get(v_a_4656_, 1);
v_fst_4661_ = lean_ctor_get(v_a_4656_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_a_4656_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4663_ = v_a_4656_;
v_isShared_4664_ = v_isSharedCheck_4687_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_snd_4660_);
lean_inc(v_fst_4661_);
lean_dec(v_a_4656_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4687_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v_stream_4665_; lean_object* v_nameMap_4666_; lean_object* v_levelMap_4667_; lean_object* v_exprMap_4668_; lean_object* v_recursorRuleMap_4669_; lean_object* v_constMap_4670_; lean_object* v_constOrder_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4686_; 
v_stream_4665_ = lean_ctor_get(v_snd_4660_, 0);
v_nameMap_4666_ = lean_ctor_get(v_snd_4660_, 1);
v_levelMap_4667_ = lean_ctor_get(v_snd_4660_, 2);
v_exprMap_4668_ = lean_ctor_get(v_snd_4660_, 3);
v_recursorRuleMap_4669_ = lean_ctor_get(v_snd_4660_, 4);
v_constMap_4670_ = lean_ctor_get(v_snd_4660_, 5);
v_constOrder_4671_ = lean_ctor_get(v_snd_4660_, 6);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_snd_4660_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4673_ = v_snd_4660_;
v_isShared_4674_ = v_isSharedCheck_4686_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_constOrder_4671_);
lean_inc(v_constMap_4670_);
lean_inc(v_recursorRuleMap_4669_);
lean_inc(v_exprMap_4668_);
lean_inc(v_levelMap_4667_);
lean_inc(v_nameMap_4666_);
lean_inc(v_stream_4665_);
lean_dec(v_snd_4660_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4686_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4675_ = lean_box(0);
v___x_4676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4668_, v_a_4422_, v_fst_4661_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 3, v___x_4676_);
v___x_4678_ = v___x_4673_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_stream_4665_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_nameMap_4666_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_levelMap_4667_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_recursorRuleMap_4669_);
lean_ctor_set(v_reuseFailAlloc_4685_, 5, v_constMap_4670_);
lean_ctor_set(v_reuseFailAlloc_4685_, 6, v_constOrder_4671_);
v___x_4678_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4680_; 
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 1, v___x_4678_);
lean_ctor_set(v___x_4663_, 0, v___x_4675_);
v___x_4680_ = v___x_4663_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4682_; 
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4680_);
v___x_4682_ = v___x_4658_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec(v_a_4422_);
v_a_4689_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4655_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4655_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4697_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4697_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4730_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4700_ = v___x_4697_;
v_isShared_4701_ = v_isSharedCheck_4730_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4730_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_snd_4702_; lean_object* v_fst_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4729_; 
v_snd_4702_ = lean_ctor_get(v_a_4698_, 1);
v_fst_4703_ = lean_ctor_get(v_a_4698_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v_a_4698_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4705_ = v_a_4698_;
v_isShared_4706_ = v_isSharedCheck_4729_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_snd_4702_);
lean_inc(v_fst_4703_);
lean_dec(v_a_4698_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4729_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_stream_4707_; lean_object* v_nameMap_4708_; lean_object* v_levelMap_4709_; lean_object* v_exprMap_4710_; lean_object* v_recursorRuleMap_4711_; lean_object* v_constMap_4712_; lean_object* v_constOrder_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4728_; 
v_stream_4707_ = lean_ctor_get(v_snd_4702_, 0);
v_nameMap_4708_ = lean_ctor_get(v_snd_4702_, 1);
v_levelMap_4709_ = lean_ctor_get(v_snd_4702_, 2);
v_exprMap_4710_ = lean_ctor_get(v_snd_4702_, 3);
v_recursorRuleMap_4711_ = lean_ctor_get(v_snd_4702_, 4);
v_constMap_4712_ = lean_ctor_get(v_snd_4702_, 5);
v_constOrder_4713_ = lean_ctor_get(v_snd_4702_, 6);
v_isSharedCheck_4728_ = !lean_is_exclusive(v_snd_4702_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4715_ = v_snd_4702_;
v_isShared_4716_ = v_isSharedCheck_4728_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_constOrder_4713_);
lean_inc(v_constMap_4712_);
lean_inc(v_recursorRuleMap_4711_);
lean_inc(v_exprMap_4710_);
lean_inc(v_levelMap_4709_);
lean_inc(v_nameMap_4708_);
lean_inc(v_stream_4707_);
lean_dec(v_snd_4702_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4728_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4720_; 
v___x_4717_ = lean_box(0);
v___x_4718_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4710_, v_a_4422_, v_fst_4703_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 3, v___x_4718_);
v___x_4720_ = v___x_4715_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_stream_4707_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v_nameMap_4708_);
lean_ctor_set(v_reuseFailAlloc_4727_, 2, v_levelMap_4709_);
lean_ctor_set(v_reuseFailAlloc_4727_, 3, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4727_, 4, v_recursorRuleMap_4711_);
lean_ctor_set(v_reuseFailAlloc_4727_, 5, v_constMap_4712_);
lean_ctor_set(v_reuseFailAlloc_4727_, 6, v_constOrder_4713_);
v___x_4720_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4722_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 1, v___x_4720_);
lean_ctor_set(v___x_4705_, 0, v___x_4717_);
v___x_4722_ = v___x_4705_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v___x_4720_);
v___x_4722_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4724_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 0, v___x_4722_);
v___x_4724_ = v___x_4700_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_dec(v_a_4422_);
v_a_4731_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4697_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4697_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4739_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4739_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4772_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4772_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4772_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_snd_4744_; lean_object* v_fst_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4771_; 
v_snd_4744_ = lean_ctor_get(v_a_4740_, 1);
v_fst_4745_ = lean_ctor_get(v_a_4740_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_a_4740_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4747_ = v_a_4740_;
v_isShared_4748_ = v_isSharedCheck_4771_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_snd_4744_);
lean_inc(v_fst_4745_);
lean_dec(v_a_4740_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4771_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v_stream_4749_; lean_object* v_nameMap_4750_; lean_object* v_levelMap_4751_; lean_object* v_exprMap_4752_; lean_object* v_recursorRuleMap_4753_; lean_object* v_constMap_4754_; lean_object* v_constOrder_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4770_; 
v_stream_4749_ = lean_ctor_get(v_snd_4744_, 0);
v_nameMap_4750_ = lean_ctor_get(v_snd_4744_, 1);
v_levelMap_4751_ = lean_ctor_get(v_snd_4744_, 2);
v_exprMap_4752_ = lean_ctor_get(v_snd_4744_, 3);
v_recursorRuleMap_4753_ = lean_ctor_get(v_snd_4744_, 4);
v_constMap_4754_ = lean_ctor_get(v_snd_4744_, 5);
v_constOrder_4755_ = lean_ctor_get(v_snd_4744_, 6);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_snd_4744_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4757_ = v_snd_4744_;
v_isShared_4758_ = v_isSharedCheck_4770_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_constOrder_4755_);
lean_inc(v_constMap_4754_);
lean_inc(v_recursorRuleMap_4753_);
lean_inc(v_exprMap_4752_);
lean_inc(v_levelMap_4751_);
lean_inc(v_nameMap_4750_);
lean_inc(v_stream_4749_);
lean_dec(v_snd_4744_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4770_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4759_ = lean_box(0);
v___x_4760_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4752_, v_a_4422_, v_fst_4745_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 3, v___x_4760_);
v___x_4762_ = v___x_4757_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_stream_4749_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_nameMap_4750_);
lean_ctor_set(v_reuseFailAlloc_4769_, 2, v_levelMap_4751_);
lean_ctor_set(v_reuseFailAlloc_4769_, 3, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4769_, 4, v_recursorRuleMap_4753_);
lean_ctor_set(v_reuseFailAlloc_4769_, 5, v_constMap_4754_);
lean_ctor_set(v_reuseFailAlloc_4769_, 6, v_constOrder_4755_);
v___x_4762_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4764_; 
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 1, v___x_4762_);
lean_ctor_set(v___x_4747_, 0, v___x_4759_);
v___x_4764_ = v___x_4747_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4766_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4764_);
v___x_4766_ = v___x_4742_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec(v_a_4422_);
v_a_4773_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4739_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4739_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4781_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4781_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_snd_4421_, v_a_4350_);
lean_dec(v_snd_4421_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4814_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4784_ = v___x_4781_;
v_isShared_4785_ = v_isSharedCheck_4814_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4781_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4814_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v_snd_4786_; lean_object* v_fst_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4813_; 
v_snd_4786_ = lean_ctor_get(v_a_4782_, 1);
v_fst_4787_ = lean_ctor_get(v_a_4782_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_a_4782_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4789_ = v_a_4782_;
v_isShared_4790_ = v_isSharedCheck_4813_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_snd_4786_);
lean_inc(v_fst_4787_);
lean_dec(v_a_4782_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4813_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v_stream_4791_; lean_object* v_nameMap_4792_; lean_object* v_levelMap_4793_; lean_object* v_exprMap_4794_; lean_object* v_recursorRuleMap_4795_; lean_object* v_constMap_4796_; lean_object* v_constOrder_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4812_; 
v_stream_4791_ = lean_ctor_get(v_snd_4786_, 0);
v_nameMap_4792_ = lean_ctor_get(v_snd_4786_, 1);
v_levelMap_4793_ = lean_ctor_get(v_snd_4786_, 2);
v_exprMap_4794_ = lean_ctor_get(v_snd_4786_, 3);
v_recursorRuleMap_4795_ = lean_ctor_get(v_snd_4786_, 4);
v_constMap_4796_ = lean_ctor_get(v_snd_4786_, 5);
v_constOrder_4797_ = lean_ctor_get(v_snd_4786_, 6);
v_isSharedCheck_4812_ = !lean_is_exclusive(v_snd_4786_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4799_ = v_snd_4786_;
v_isShared_4800_ = v_isSharedCheck_4812_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_constOrder_4797_);
lean_inc(v_constMap_4796_);
lean_inc(v_recursorRuleMap_4795_);
lean_inc(v_exprMap_4794_);
lean_inc(v_levelMap_4793_);
lean_inc(v_nameMap_4792_);
lean_inc(v_stream_4791_);
lean_dec(v_snd_4786_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4812_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4801_ = lean_box(0);
v___x_4802_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4794_, v_a_4422_, v_fst_4787_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 3, v___x_4802_);
v___x_4804_ = v___x_4799_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_stream_4791_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_nameMap_4792_);
lean_ctor_set(v_reuseFailAlloc_4811_, 2, v_levelMap_4793_);
lean_ctor_set(v_reuseFailAlloc_4811_, 3, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4811_, 4, v_recursorRuleMap_4795_);
lean_ctor_set(v_reuseFailAlloc_4811_, 5, v_constMap_4796_);
lean_ctor_set(v_reuseFailAlloc_4811_, 6, v_constOrder_4797_);
v___x_4804_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4806_; 
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 1, v___x_4804_);
lean_ctor_set(v___x_4789_, 0, v___x_4801_);
v___x_4806_ = v___x_4789_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
lean_object* v___x_4808_; 
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v___x_4806_);
v___x_4808_ = v___x_4784_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
lean_dec(v_a_4422_);
v_a_4815_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4781_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4781_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4823_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4823_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_snd_4421_, v_a_4350_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4856_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4856_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4856_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v_snd_4828_; lean_object* v_fst_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4855_; 
v_snd_4828_ = lean_ctor_get(v_a_4824_, 1);
v_fst_4829_ = lean_ctor_get(v_a_4824_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v_a_4824_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4831_ = v_a_4824_;
v_isShared_4832_ = v_isSharedCheck_4855_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_snd_4828_);
lean_inc(v_fst_4829_);
lean_dec(v_a_4824_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4855_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v_stream_4833_; lean_object* v_nameMap_4834_; lean_object* v_levelMap_4835_; lean_object* v_exprMap_4836_; lean_object* v_recursorRuleMap_4837_; lean_object* v_constMap_4838_; lean_object* v_constOrder_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4854_; 
v_stream_4833_ = lean_ctor_get(v_snd_4828_, 0);
v_nameMap_4834_ = lean_ctor_get(v_snd_4828_, 1);
v_levelMap_4835_ = lean_ctor_get(v_snd_4828_, 2);
v_exprMap_4836_ = lean_ctor_get(v_snd_4828_, 3);
v_recursorRuleMap_4837_ = lean_ctor_get(v_snd_4828_, 4);
v_constMap_4838_ = lean_ctor_get(v_snd_4828_, 5);
v_constOrder_4839_ = lean_ctor_get(v_snd_4828_, 6);
v_isSharedCheck_4854_ = !lean_is_exclusive(v_snd_4828_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4841_ = v_snd_4828_;
v_isShared_4842_ = v_isSharedCheck_4854_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_constOrder_4839_);
lean_inc(v_constMap_4838_);
lean_inc(v_recursorRuleMap_4837_);
lean_inc(v_exprMap_4836_);
lean_inc(v_levelMap_4835_);
lean_inc(v_nameMap_4834_);
lean_inc(v_stream_4833_);
lean_dec(v_snd_4828_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4854_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4846_; 
v___x_4843_ = lean_box(0);
v___x_4844_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4836_, v_a_4422_, v_fst_4829_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 3, v___x_4844_);
v___x_4846_ = v___x_4841_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_stream_4833_);
lean_ctor_set(v_reuseFailAlloc_4853_, 1, v_nameMap_4834_);
lean_ctor_set(v_reuseFailAlloc_4853_, 2, v_levelMap_4835_);
lean_ctor_set(v_reuseFailAlloc_4853_, 3, v___x_4844_);
lean_ctor_set(v_reuseFailAlloc_4853_, 4, v_recursorRuleMap_4837_);
lean_ctor_set(v_reuseFailAlloc_4853_, 5, v_constMap_4838_);
lean_ctor_set(v_reuseFailAlloc_4853_, 6, v_constOrder_4839_);
v___x_4846_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
lean_object* v___x_4848_; 
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 1, v___x_4846_);
lean_ctor_set(v___x_4831_, 0, v___x_4843_);
v___x_4848_ = v___x_4831_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
lean_object* v___x_4850_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4848_);
v___x_4850_ = v___x_4826_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
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
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec(v_a_4422_);
v_a_4857_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4823_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4823_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
else
{
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4420_);
if (lean_obj_tag(v_tail_4419_) == 0)
{
lean_object* v___x_4865_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4865_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_snd_4421_, v_a_4350_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4898_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4898_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4898_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v_snd_4870_; lean_object* v_fst_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4897_; 
v_snd_4870_ = lean_ctor_get(v_a_4866_, 1);
v_fst_4871_ = lean_ctor_get(v_a_4866_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_a_4866_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4873_ = v_a_4866_;
v_isShared_4874_ = v_isSharedCheck_4897_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_snd_4870_);
lean_inc(v_fst_4871_);
lean_dec(v_a_4866_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4897_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v_stream_4875_; lean_object* v_nameMap_4876_; lean_object* v_levelMap_4877_; lean_object* v_exprMap_4878_; lean_object* v_recursorRuleMap_4879_; lean_object* v_constMap_4880_; lean_object* v_constOrder_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4896_; 
v_stream_4875_ = lean_ctor_get(v_snd_4870_, 0);
v_nameMap_4876_ = lean_ctor_get(v_snd_4870_, 1);
v_levelMap_4877_ = lean_ctor_get(v_snd_4870_, 2);
v_exprMap_4878_ = lean_ctor_get(v_snd_4870_, 3);
v_recursorRuleMap_4879_ = lean_ctor_get(v_snd_4870_, 4);
v_constMap_4880_ = lean_ctor_get(v_snd_4870_, 5);
v_constOrder_4881_ = lean_ctor_get(v_snd_4870_, 6);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_snd_4870_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4883_ = v_snd_4870_;
v_isShared_4884_ = v_isSharedCheck_4896_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_constOrder_4881_);
lean_inc(v_constMap_4880_);
lean_inc(v_recursorRuleMap_4879_);
lean_inc(v_exprMap_4878_);
lean_inc(v_levelMap_4877_);
lean_inc(v_nameMap_4876_);
lean_inc(v_stream_4875_);
lean_dec(v_snd_4870_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4896_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4885_ = lean_box(0);
v___x_4886_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4878_, v_a_4422_, v_fst_4871_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 3, v___x_4886_);
v___x_4888_ = v___x_4883_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_stream_4875_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_nameMap_4876_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_levelMap_4877_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v___x_4886_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v_recursorRuleMap_4879_);
lean_ctor_set(v_reuseFailAlloc_4895_, 5, v_constMap_4880_);
lean_ctor_set(v_reuseFailAlloc_4895_, 6, v_constOrder_4881_);
v___x_4888_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4890_; 
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 1, v___x_4888_);
lean_ctor_set(v___x_4873_, 0, v___x_4885_);
v___x_4890_ = v___x_4873_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4892_; 
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4890_);
v___x_4892_ = v___x_4868_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
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
lean_dec(v_a_4422_);
v_a_4899_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4865_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4865_);
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
lean_dec(v_a_4422_);
lean_dec(v_snd_4421_);
lean_dec(v_tail_4419_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_mantissa_4412_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_exponent_4413_);
lean_dec(v_mantissa_4412_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 2)
{
lean_object* v_n_4907_; lean_object* v_mantissa_4908_; lean_object* v_exponent_4909_; lean_object* v_natZero_4910_; lean_object* v_intZero_4911_; uint8_t v_isNeg_4912_; 
v_n_4907_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc_ref(v_n_4907_);
lean_dec_ref_known(v_snd_4379_, 1);
v_mantissa_4908_ = lean_ctor_get(v_n_4907_, 0);
lean_inc(v_mantissa_4908_);
v_exponent_4909_ = lean_ctor_get(v_n_4907_, 1);
lean_inc(v_exponent_4909_);
lean_dec_ref(v_n_4907_);
v_natZero_4910_ = lean_unsigned_to_nat(0u);
v_intZero_4911_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4912_ = lean_int_dec_lt(v_mantissa_4908_, v_intZero_4911_);
if (v_isNeg_4912_ == 0)
{
uint8_t v___x_4913_; 
v___x_4913_ = lean_nat_dec_eq(v_exponent_4909_, v_natZero_4910_);
lean_dec(v_exponent_4909_);
if (v___x_4913_ == 0)
{
lean_dec(v_mantissa_4908_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_4380_) == 1)
{
lean_object* v_head_4914_; lean_object* v_tail_4915_; lean_object* v_fst_4916_; lean_object* v_snd_4917_; lean_object* v_a_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v_head_4914_ = lean_ctor_get(v_tail_4380_, 0);
lean_inc(v_head_4914_);
v_tail_4915_ = lean_ctor_get(v_tail_4380_, 1);
lean_inc(v_tail_4915_);
lean_dec_ref_known(v_tail_4380_, 2);
v_fst_4916_ = lean_ctor_get(v_head_4914_, 0);
lean_inc(v_fst_4916_);
v_snd_4917_ = lean_ctor_get(v_head_4914_, 1);
lean_inc(v_snd_4917_);
lean_dec(v_head_4914_);
v_a_4918_ = lean_nat_abs(v_mantissa_4908_);
lean_dec(v_mantissa_4908_);
v___x_4919_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20));
v___x_4920_ = lean_string_dec_eq(v_fst_4916_, v___x_4919_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; uint8_t v___x_4922_; 
v___x_4921_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21));
v___x_4922_ = lean_string_dec_eq(v_fst_4916_, v___x_4921_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22));
v___x_4924_ = lean_string_dec_eq(v_fst_4916_, v___x_4923_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; uint8_t v___x_4926_; 
v___x_4925_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23));
v___x_4926_ = lean_string_dec_eq(v_fst_4916_, v___x_4925_);
lean_dec(v_fst_4916_);
if (v___x_4926_ == 0)
{
lean_dec(v_a_4918_);
lean_dec(v_snd_4917_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_4915_) == 0)
{
lean_object* v___x_4927_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4927_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_snd_4917_, v_a_4350_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4960_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4960_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4960_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v_snd_4932_; lean_object* v_fst_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4959_; 
v_snd_4932_ = lean_ctor_get(v_a_4928_, 1);
v_fst_4933_ = lean_ctor_get(v_a_4928_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v_a_4928_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4935_ = v_a_4928_;
v_isShared_4936_ = v_isSharedCheck_4959_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_snd_4932_);
lean_inc(v_fst_4933_);
lean_dec(v_a_4928_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4959_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v_stream_4937_; lean_object* v_nameMap_4938_; lean_object* v_levelMap_4939_; lean_object* v_exprMap_4940_; lean_object* v_recursorRuleMap_4941_; lean_object* v_constMap_4942_; lean_object* v_constOrder_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4958_; 
v_stream_4937_ = lean_ctor_get(v_snd_4932_, 0);
v_nameMap_4938_ = lean_ctor_get(v_snd_4932_, 1);
v_levelMap_4939_ = lean_ctor_get(v_snd_4932_, 2);
v_exprMap_4940_ = lean_ctor_get(v_snd_4932_, 3);
v_recursorRuleMap_4941_ = lean_ctor_get(v_snd_4932_, 4);
v_constMap_4942_ = lean_ctor_get(v_snd_4932_, 5);
v_constOrder_4943_ = lean_ctor_get(v_snd_4932_, 6);
v_isSharedCheck_4958_ = !lean_is_exclusive(v_snd_4932_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4945_ = v_snd_4932_;
v_isShared_4946_ = v_isSharedCheck_4958_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_constOrder_4943_);
lean_inc(v_constMap_4942_);
lean_inc(v_recursorRuleMap_4941_);
lean_inc(v_exprMap_4940_);
lean_inc(v_levelMap_4939_);
lean_inc(v_nameMap_4938_);
lean_inc(v_stream_4937_);
lean_dec(v_snd_4932_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4958_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4950_; 
v___x_4947_ = lean_box(0);
v___x_4948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_4939_, v_a_4918_, v_fst_4933_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 2, v___x_4948_);
v___x_4950_ = v___x_4945_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_stream_4937_);
lean_ctor_set(v_reuseFailAlloc_4957_, 1, v_nameMap_4938_);
lean_ctor_set(v_reuseFailAlloc_4957_, 2, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4957_, 3, v_exprMap_4940_);
lean_ctor_set(v_reuseFailAlloc_4957_, 4, v_recursorRuleMap_4941_);
lean_ctor_set(v_reuseFailAlloc_4957_, 5, v_constMap_4942_);
lean_ctor_set(v_reuseFailAlloc_4957_, 6, v_constOrder_4943_);
v___x_4950_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
lean_object* v___x_4952_; 
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 1, v___x_4950_);
lean_ctor_set(v___x_4935_, 0, v___x_4947_);
v___x_4952_ = v___x_4935_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4947_);
lean_ctor_set(v_reuseFailAlloc_4956_, 1, v___x_4950_);
v___x_4952_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
lean_object* v___x_4954_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4952_);
v___x_4954_ = v___x_4930_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4952_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec(v_a_4918_);
v_a_4961_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4927_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4927_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
else
{
lean_dec(v_a_4918_);
lean_dec(v_snd_4917_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4916_);
if (lean_obj_tag(v_tail_4915_) == 0)
{
lean_object* v___x_4969_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_4969_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_snd_4917_, v_a_4350_);
lean_dec(v_snd_4917_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_5002_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_5002_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_5002_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v_snd_4974_; lean_object* v_fst_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5001_; 
v_snd_4974_ = lean_ctor_get(v_a_4970_, 1);
v_fst_4975_ = lean_ctor_get(v_a_4970_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_a_4970_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4977_ = v_a_4970_;
v_isShared_4978_ = v_isSharedCheck_5001_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_snd_4974_);
lean_inc(v_fst_4975_);
lean_dec(v_a_4970_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5001_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v_stream_4979_; lean_object* v_nameMap_4980_; lean_object* v_levelMap_4981_; lean_object* v_exprMap_4982_; lean_object* v_recursorRuleMap_4983_; lean_object* v_constMap_4984_; lean_object* v_constOrder_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_5000_; 
v_stream_4979_ = lean_ctor_get(v_snd_4974_, 0);
v_nameMap_4980_ = lean_ctor_get(v_snd_4974_, 1);
v_levelMap_4981_ = lean_ctor_get(v_snd_4974_, 2);
v_exprMap_4982_ = lean_ctor_get(v_snd_4974_, 3);
v_recursorRuleMap_4983_ = lean_ctor_get(v_snd_4974_, 4);
v_constMap_4984_ = lean_ctor_get(v_snd_4974_, 5);
v_constOrder_4985_ = lean_ctor_get(v_snd_4974_, 6);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_snd_4974_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4987_ = v_snd_4974_;
v_isShared_4988_ = v_isSharedCheck_5000_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_constOrder_4985_);
lean_inc(v_constMap_4984_);
lean_inc(v_recursorRuleMap_4983_);
lean_inc(v_exprMap_4982_);
lean_inc(v_levelMap_4981_);
lean_inc(v_nameMap_4980_);
lean_inc(v_stream_4979_);
lean_dec(v_snd_4974_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_5000_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4992_; 
v___x_4989_ = lean_box(0);
v___x_4990_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_4981_, v_a_4918_, v_fst_4975_);
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 2, v___x_4990_);
v___x_4992_ = v___x_4987_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_stream_4979_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_nameMap_4980_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v___x_4990_);
lean_ctor_set(v_reuseFailAlloc_4999_, 3, v_exprMap_4982_);
lean_ctor_set(v_reuseFailAlloc_4999_, 4, v_recursorRuleMap_4983_);
lean_ctor_set(v_reuseFailAlloc_4999_, 5, v_constMap_4984_);
lean_ctor_set(v_reuseFailAlloc_4999_, 6, v_constOrder_4985_);
v___x_4992_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4994_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_4992_);
lean_ctor_set(v___x_4977_, 0, v___x_4989_);
v___x_4994_ = v___x_4977_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4989_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4996_; 
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v___x_4994_);
v___x_4996_ = v___x_4972_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec(v_a_4918_);
v_a_5003_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4969_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4969_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
else
{
lean_dec(v_a_4918_);
lean_dec(v_snd_4917_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4916_);
if (lean_obj_tag(v_tail_4915_) == 0)
{
lean_object* v___x_5011_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_5011_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_snd_4917_, v_a_4350_);
lean_dec(v_snd_4917_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5044_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5044_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5044_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v_snd_5016_; lean_object* v_fst_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5043_; 
v_snd_5016_ = lean_ctor_get(v_a_5012_, 1);
v_fst_5017_ = lean_ctor_get(v_a_5012_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_a_5012_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5019_ = v_a_5012_;
v_isShared_5020_ = v_isSharedCheck_5043_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_snd_5016_);
lean_inc(v_fst_5017_);
lean_dec(v_a_5012_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5043_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v_stream_5021_; lean_object* v_nameMap_5022_; lean_object* v_levelMap_5023_; lean_object* v_exprMap_5024_; lean_object* v_recursorRuleMap_5025_; lean_object* v_constMap_5026_; lean_object* v_constOrder_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5042_; 
v_stream_5021_ = lean_ctor_get(v_snd_5016_, 0);
v_nameMap_5022_ = lean_ctor_get(v_snd_5016_, 1);
v_levelMap_5023_ = lean_ctor_get(v_snd_5016_, 2);
v_exprMap_5024_ = lean_ctor_get(v_snd_5016_, 3);
v_recursorRuleMap_5025_ = lean_ctor_get(v_snd_5016_, 4);
v_constMap_5026_ = lean_ctor_get(v_snd_5016_, 5);
v_constOrder_5027_ = lean_ctor_get(v_snd_5016_, 6);
v_isSharedCheck_5042_ = !lean_is_exclusive(v_snd_5016_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5029_ = v_snd_5016_;
v_isShared_5030_ = v_isSharedCheck_5042_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_constOrder_5027_);
lean_inc(v_constMap_5026_);
lean_inc(v_recursorRuleMap_5025_);
lean_inc(v_exprMap_5024_);
lean_inc(v_levelMap_5023_);
lean_inc(v_nameMap_5022_);
lean_inc(v_stream_5021_);
lean_dec(v_snd_5016_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5042_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5031_ = lean_box(0);
v___x_5032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5023_, v_a_4918_, v_fst_5017_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 2, v___x_5032_);
v___x_5034_ = v___x_5029_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_stream_5021_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v_nameMap_5022_);
lean_ctor_set(v_reuseFailAlloc_5041_, 2, v___x_5032_);
lean_ctor_set(v_reuseFailAlloc_5041_, 3, v_exprMap_5024_);
lean_ctor_set(v_reuseFailAlloc_5041_, 4, v_recursorRuleMap_5025_);
lean_ctor_set(v_reuseFailAlloc_5041_, 5, v_constMap_5026_);
lean_ctor_set(v_reuseFailAlloc_5041_, 6, v_constOrder_5027_);
v___x_5034_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5036_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 1, v___x_5034_);
lean_ctor_set(v___x_5019_, 0, v___x_5031_);
v___x_5036_ = v___x_5019_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5031_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5038_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___x_5036_);
v___x_5038_ = v___x_5014_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec(v_a_4918_);
v_a_5045_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5011_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5011_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
else
{
lean_dec(v_a_4918_);
lean_dec(v_snd_4917_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_4916_);
if (lean_obj_tag(v_tail_4915_) == 0)
{
lean_object* v___x_5053_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_5053_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_snd_4917_, v_a_4350_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5086_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5086_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5086_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v_snd_5058_; lean_object* v_fst_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5085_; 
v_snd_5058_ = lean_ctor_get(v_a_5054_, 1);
v_fst_5059_ = lean_ctor_get(v_a_5054_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_a_5054_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5061_ = v_a_5054_;
v_isShared_5062_ = v_isSharedCheck_5085_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_snd_5058_);
lean_inc(v_fst_5059_);
lean_dec(v_a_5054_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5085_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v_stream_5063_; lean_object* v_nameMap_5064_; lean_object* v_levelMap_5065_; lean_object* v_exprMap_5066_; lean_object* v_recursorRuleMap_5067_; lean_object* v_constMap_5068_; lean_object* v_constOrder_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5084_; 
v_stream_5063_ = lean_ctor_get(v_snd_5058_, 0);
v_nameMap_5064_ = lean_ctor_get(v_snd_5058_, 1);
v_levelMap_5065_ = lean_ctor_get(v_snd_5058_, 2);
v_exprMap_5066_ = lean_ctor_get(v_snd_5058_, 3);
v_recursorRuleMap_5067_ = lean_ctor_get(v_snd_5058_, 4);
v_constMap_5068_ = lean_ctor_get(v_snd_5058_, 5);
v_constOrder_5069_ = lean_ctor_get(v_snd_5058_, 6);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_snd_5058_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5071_ = v_snd_5058_;
v_isShared_5072_ = v_isSharedCheck_5084_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_constOrder_5069_);
lean_inc(v_constMap_5068_);
lean_inc(v_recursorRuleMap_5067_);
lean_inc(v_exprMap_5066_);
lean_inc(v_levelMap_5065_);
lean_inc(v_nameMap_5064_);
lean_inc(v_stream_5063_);
lean_dec(v_snd_5058_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5084_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5073_ = lean_box(0);
v___x_5074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5065_, v_a_4918_, v_fst_5059_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 2, v___x_5074_);
v___x_5076_ = v___x_5071_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_stream_5063_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_nameMap_5064_);
lean_ctor_set(v_reuseFailAlloc_5083_, 2, v___x_5074_);
lean_ctor_set(v_reuseFailAlloc_5083_, 3, v_exprMap_5066_);
lean_ctor_set(v_reuseFailAlloc_5083_, 4, v_recursorRuleMap_5067_);
lean_ctor_set(v_reuseFailAlloc_5083_, 5, v_constMap_5068_);
lean_ctor_set(v_reuseFailAlloc_5083_, 6, v_constOrder_5069_);
v___x_5076_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5078_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 1, v___x_5076_);
lean_ctor_set(v___x_5061_, 0, v___x_5073_);
v___x_5078_ = v___x_5061_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v___x_5076_);
v___x_5078_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5078_);
v___x_5080_ = v___x_5056_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_a_4918_);
v_a_5087_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5053_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5053_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
else
{
lean_dec(v_a_4918_);
lean_dec(v_snd_4917_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_mantissa_4908_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_exponent_4909_);
lean_dec(v_mantissa_4908_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec_ref(v_fst_4378_);
if (lean_obj_tag(v_snd_4379_) == 2)
{
lean_object* v_n_5095_; lean_object* v_mantissa_5096_; lean_object* v_exponent_5097_; lean_object* v_natZero_5098_; lean_object* v_intZero_5099_; uint8_t v_isNeg_5100_; 
v_n_5095_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc_ref(v_n_5095_);
lean_dec_ref_known(v_snd_4379_, 1);
v_mantissa_5096_ = lean_ctor_get(v_n_5095_, 0);
lean_inc(v_mantissa_5096_);
v_exponent_5097_ = lean_ctor_get(v_n_5095_, 1);
lean_inc(v_exponent_5097_);
lean_dec_ref(v_n_5095_);
v_natZero_5098_ = lean_unsigned_to_nat(0u);
v_intZero_5099_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5100_ = lean_int_dec_lt(v_mantissa_5096_, v_intZero_5099_);
if (v_isNeg_5100_ == 0)
{
uint8_t v___x_5101_; 
v___x_5101_ = lean_nat_dec_eq(v_exponent_5097_, v_natZero_5098_);
lean_dec(v_exponent_5097_);
if (v___x_5101_ == 0)
{
lean_dec(v_mantissa_5096_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_4380_) == 1)
{
lean_object* v_head_5102_; lean_object* v_tail_5103_; lean_object* v_fst_5104_; lean_object* v_snd_5105_; lean_object* v_a_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
v_head_5102_ = lean_ctor_get(v_tail_4380_, 0);
lean_inc(v_head_5102_);
v_tail_5103_ = lean_ctor_get(v_tail_4380_, 1);
lean_inc(v_tail_5103_);
lean_dec_ref_known(v_tail_4380_, 2);
v_fst_5104_ = lean_ctor_get(v_head_5102_, 0);
lean_inc(v_fst_5104_);
v_snd_5105_ = lean_ctor_get(v_head_5102_, 1);
lean_inc(v_snd_5105_);
lean_dec(v_head_5102_);
v_a_5106_ = lean_nat_abs(v_mantissa_5096_);
lean_dec(v_mantissa_5096_);
v___x_5107_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_5108_ = lean_string_dec_eq(v_fst_5104_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; uint8_t v___x_5110_; 
v___x_5109_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24));
v___x_5110_ = lean_string_dec_eq(v_fst_5104_, v___x_5109_);
lean_dec(v_fst_5104_);
if (v___x_5110_ == 0)
{
lean_dec(v_a_5106_);
lean_dec(v_snd_5105_);
lean_dec(v_tail_5103_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_tail_5103_) == 0)
{
lean_object* v___x_5111_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_5111_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_snd_5105_, v_a_4350_);
lean_dec(v_snd_5105_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5144_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5144_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5144_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v_snd_5116_; lean_object* v_fst_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5143_; 
v_snd_5116_ = lean_ctor_get(v_a_5112_, 1);
v_fst_5117_ = lean_ctor_get(v_a_5112_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v_a_5112_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5119_ = v_a_5112_;
v_isShared_5120_ = v_isSharedCheck_5143_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_snd_5116_);
lean_inc(v_fst_5117_);
lean_dec(v_a_5112_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5143_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v_stream_5121_; lean_object* v_nameMap_5122_; lean_object* v_levelMap_5123_; lean_object* v_exprMap_5124_; lean_object* v_recursorRuleMap_5125_; lean_object* v_constMap_5126_; lean_object* v_constOrder_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5142_; 
v_stream_5121_ = lean_ctor_get(v_snd_5116_, 0);
v_nameMap_5122_ = lean_ctor_get(v_snd_5116_, 1);
v_levelMap_5123_ = lean_ctor_get(v_snd_5116_, 2);
v_exprMap_5124_ = lean_ctor_get(v_snd_5116_, 3);
v_recursorRuleMap_5125_ = lean_ctor_get(v_snd_5116_, 4);
v_constMap_5126_ = lean_ctor_get(v_snd_5116_, 5);
v_constOrder_5127_ = lean_ctor_get(v_snd_5116_, 6);
v_isSharedCheck_5142_ = !lean_is_exclusive(v_snd_5116_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5129_ = v_snd_5116_;
v_isShared_5130_ = v_isSharedCheck_5142_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_constOrder_5127_);
lean_inc(v_constMap_5126_);
lean_inc(v_recursorRuleMap_5125_);
lean_inc(v_exprMap_5124_);
lean_inc(v_levelMap_5123_);
lean_inc(v_nameMap_5122_);
lean_inc(v_stream_5121_);
lean_dec(v_snd_5116_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5142_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5134_; 
v___x_5131_ = lean_box(0);
v___x_5132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5122_, v_a_5106_, v_fst_5117_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 1, v___x_5132_);
v___x_5134_ = v___x_5129_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_stream_5121_);
lean_ctor_set(v_reuseFailAlloc_5141_, 1, v___x_5132_);
lean_ctor_set(v_reuseFailAlloc_5141_, 2, v_levelMap_5123_);
lean_ctor_set(v_reuseFailAlloc_5141_, 3, v_exprMap_5124_);
lean_ctor_set(v_reuseFailAlloc_5141_, 4, v_recursorRuleMap_5125_);
lean_ctor_set(v_reuseFailAlloc_5141_, 5, v_constMap_5126_);
lean_ctor_set(v_reuseFailAlloc_5141_, 6, v_constOrder_5127_);
v___x_5134_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
lean_object* v___x_5136_; 
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 1, v___x_5134_);
lean_ctor_set(v___x_5119_, 0, v___x_5131_);
v___x_5136_ = v___x_5119_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5140_, 1, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
lean_object* v___x_5138_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 0, v___x_5136_);
v___x_5138_ = v___x_5114_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5136_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_a_5106_);
v_a_5145_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5111_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5111_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_dec(v_a_5106_);
lean_dec(v_snd_5105_);
lean_dec(v_tail_5103_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_fst_5104_);
if (lean_obj_tag(v_tail_5103_) == 0)
{
lean_object* v___x_5153_; 
lean_del_object(v___x_4363_);
lean_dec(v_kvPairs_4361_);
lean_del_object(v___x_4359_);
v___x_5153_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_snd_5105_, v_a_4350_);
lean_dec(v_snd_5105_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5186_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5156_ = v___x_5153_;
v_isShared_5157_ = v_isSharedCheck_5186_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5153_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5186_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v_snd_5158_; lean_object* v_fst_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5185_; 
v_snd_5158_ = lean_ctor_get(v_a_5154_, 1);
v_fst_5159_ = lean_ctor_get(v_a_5154_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v_a_5154_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5161_ = v_a_5154_;
v_isShared_5162_ = v_isSharedCheck_5185_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_snd_5158_);
lean_inc(v_fst_5159_);
lean_dec(v_a_5154_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5185_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v_stream_5163_; lean_object* v_nameMap_5164_; lean_object* v_levelMap_5165_; lean_object* v_exprMap_5166_; lean_object* v_recursorRuleMap_5167_; lean_object* v_constMap_5168_; lean_object* v_constOrder_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5184_; 
v_stream_5163_ = lean_ctor_get(v_snd_5158_, 0);
v_nameMap_5164_ = lean_ctor_get(v_snd_5158_, 1);
v_levelMap_5165_ = lean_ctor_get(v_snd_5158_, 2);
v_exprMap_5166_ = lean_ctor_get(v_snd_5158_, 3);
v_recursorRuleMap_5167_ = lean_ctor_get(v_snd_5158_, 4);
v_constMap_5168_ = lean_ctor_get(v_snd_5158_, 5);
v_constOrder_5169_ = lean_ctor_get(v_snd_5158_, 6);
v_isSharedCheck_5184_ = !lean_is_exclusive(v_snd_5158_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5171_ = v_snd_5158_;
v_isShared_5172_ = v_isSharedCheck_5184_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_constOrder_5169_);
lean_inc(v_constMap_5168_);
lean_inc(v_recursorRuleMap_5167_);
lean_inc(v_exprMap_5166_);
lean_inc(v_levelMap_5165_);
lean_inc(v_nameMap_5164_);
lean_inc(v_stream_5163_);
lean_dec(v_snd_5158_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5184_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5176_; 
v___x_5173_ = lean_box(0);
v___x_5174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5164_, v_a_5106_, v_fst_5159_);
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 1, v___x_5174_);
v___x_5176_ = v___x_5171_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_stream_5163_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v___x_5174_);
lean_ctor_set(v_reuseFailAlloc_5183_, 2, v_levelMap_5165_);
lean_ctor_set(v_reuseFailAlloc_5183_, 3, v_exprMap_5166_);
lean_ctor_set(v_reuseFailAlloc_5183_, 4, v_recursorRuleMap_5167_);
lean_ctor_set(v_reuseFailAlloc_5183_, 5, v_constMap_5168_);
lean_ctor_set(v_reuseFailAlloc_5183_, 6, v_constOrder_5169_);
v___x_5176_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
lean_object* v___x_5178_; 
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 1, v___x_5176_);
lean_ctor_set(v___x_5161_, 0, v___x_5173_);
v___x_5178_ = v___x_5161_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5173_);
lean_ctor_set(v_reuseFailAlloc_5182_, 1, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
lean_object* v___x_5180_; 
if (v_isShared_5157_ == 0)
{
lean_ctor_set(v___x_5156_, 0, v___x_5178_);
v___x_5180_ = v___x_5156_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5178_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec(v_a_5106_);
v_a_5187_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5153_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5153_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
else
{
lean_dec(v_a_5106_);
lean_dec(v_snd_5105_);
lean_dec(v_tail_5103_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_mantissa_5096_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
else
{
lean_dec(v_exponent_5097_);
lean_dec(v_mantissa_5096_);
lean_dec(v_tail_4380_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
else
{
lean_dec(v_tail_4380_);
lean_dec(v_snd_4379_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
v___jp_5195_:
{
if (lean_obj_tag(v___y_5196_) == 1)
{
lean_object* v_head_5197_; lean_object* v_tail_5198_; lean_object* v_fst_5199_; lean_object* v_snd_5200_; 
v_head_5197_ = lean_ctor_get(v___y_5196_, 0);
lean_inc(v_head_5197_);
v_tail_5198_ = lean_ctor_get(v___y_5196_, 1);
lean_inc(v_tail_5198_);
lean_dec_ref_known(v___y_5196_, 2);
v_fst_5199_ = lean_ctor_get(v_head_5197_, 0);
lean_inc(v_fst_5199_);
v_snd_5200_ = lean_ctor_get(v_head_5197_, 1);
lean_inc(v_snd_5200_);
lean_dec(v_head_5197_);
v_fst_4378_ = v_fst_5199_;
v_snd_4379_ = v_snd_5200_;
v_tail_4380_ = v_tail_5198_;
goto v___jp_4377_;
}
else
{
lean_dec(v___y_5196_);
lean_dec_ref(v_a_4350_);
goto v___jp_4365_;
}
}
}
}
else
{
lean_del_object(v___x_4359_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4350_);
goto v___jp_4352_;
}
}
}
else
{
lean_dec_ref(v___x_4356_);
lean_dec_ref(v_a_4350_);
goto v___jp_4352_;
}
v___jp_4352_:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4353_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1));
v___x_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
return v___x_4354_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___boxed(lean_object* v_line_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_line_5231_, v_a_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(lean_object* v_a_5235_){
_start:
{
lean_object* v_stream_5237_; lean_object* v_getLine_5238_; lean_object* v___x_5239_; 
v_stream_5237_ = lean_ctor_get(v_a_5235_, 0);
v_getLine_5238_ = lean_ctor_get(v_stream_5237_, 3);
lean_inc_ref(v_getLine_5238_);
v___x_5239_ = lean_apply_1(v_getLine_5238_, lean_box(0));
if (lean_obj_tag(v___x_5239_) == 0)
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5256_; 
v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5239_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5242_ = v___x_5239_;
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5239_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; uint8_t v___x_5246_; 
v___x_5244_ = lean_string_utf8_byte_size(v_a_5240_);
v___x_5245_ = lean_unsigned_to_nat(0u);
v___x_5246_ = lean_nat_dec_eq(v___x_5244_, v___x_5245_);
if (v___x_5246_ == 0)
{
lean_object* v___x_5247_; 
lean_del_object(v___x_5242_);
v___x_5247_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_a_5240_, v_a_5235_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v_snd_5249_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v_snd_5249_ = lean_ctor_get(v_a_5248_, 1);
lean_inc(v_snd_5249_);
lean_dec(v_a_5248_);
v_a_5235_ = v_snd_5249_;
goto _start;
}
else
{
return v___x_5247_;
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5254_; 
lean_dec(v_a_5240_);
v___x_5251_ = lean_box(0);
v___x_5252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
lean_ctor_set(v___x_5252_, 1, v_a_5235_);
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___x_5252_);
v___x_5254_ = v___x_5242_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5252_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
lean_dec_ref(v_a_5235_);
v_a_5257_ = lean_ctor_get(v___x_5239_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5239_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5239_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5239_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go___boxed(lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5265_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(lean_object* v_a_5268_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5268_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems___boxed(lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(v_a_5271_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(lean_object* v_a_5274_){
_start:
{
lean_object* v_stream_5276_; lean_object* v_getLine_5277_; lean_object* v___x_5278_; 
v_stream_5276_ = lean_ctor_get(v_a_5274_, 0);
v_getLine_5277_ = lean_ctor_get(v_stream_5276_, 3);
lean_inc_ref(v_getLine_5277_);
v___x_5278_ = lean_apply_1(v_getLine_5277_, lean_box(0));
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5287_; 
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v___x_5278_, 0);
lean_dec(v_unused_5288_);
v___x_5280_ = v___x_5278_;
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
else
{
lean_dec(v___x_5278_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5285_; 
v___x_5282_ = lean_box(0);
v___x_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
lean_ctor_set(v___x_5283_, 1, v_a_5274_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5283_);
v___x_5285_ = v___x_5280_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_dec_ref(v_a_5274_);
v_a_5289_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5278_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5278_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata___boxed(lean_object* v_a_5297_, lean_object* v_a_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5297_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(lean_object* v_a_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5300_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v_snd_5304_; lean_object* v___x_5305_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref_known(v___x_5302_, 1);
v_snd_5304_ = lean_ctor_get(v_a_5303_, 1);
lean_inc(v_snd_5304_);
lean_dec(v_a_5303_);
v___x_5305_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_snd_5304_);
return v___x_5305_;
}
else
{
return v___x_5302_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed(lean_object* v_a_5306_, lean_object* v_a_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(v_a_5306_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream(lean_object* v_stream_5309_){
_start:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5311_ = lean_alloc_closure((void*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed), 2, 0);
v___x_5312_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v___x_5311_, v_stream_5309_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5331_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5331_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5331_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v_snd_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5329_; 
v_snd_5317_ = lean_ctor_get(v_a_5313_, 1);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_a_5313_);
if (v_isSharedCheck_5329_ == 0)
{
lean_object* v_unused_5330_; 
v_unused_5330_ = lean_ctor_get(v_a_5313_, 0);
lean_dec(v_unused_5330_);
v___x_5319_ = v_a_5313_;
v_isShared_5320_ = v_isSharedCheck_5329_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_snd_5317_);
lean_dec(v_a_5313_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5329_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v_constMap_5321_; lean_object* v_constOrder_5322_; lean_object* v___x_5324_; 
v_constMap_5321_ = lean_ctor_get(v_snd_5317_, 5);
lean_inc_ref(v_constMap_5321_);
v_constOrder_5322_ = lean_ctor_get(v_snd_5317_, 6);
lean_inc_ref(v_constOrder_5322_);
lean_dec(v_snd_5317_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 1, v_constOrder_5322_);
lean_ctor_set(v___x_5319_, 0, v_constMap_5321_);
v___x_5324_ = v___x_5319_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_constMap_5321_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v_constOrder_5322_);
v___x_5324_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5326_; 
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5324_);
v___x_5326_ = v___x_5315_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
else
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5339_; 
v_a_5332_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5339_ == 0)
{
v___x_5334_ = v___x_5312_;
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v___x_5312_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5337_; 
if (v_isShared_5335_ == 0)
{
v___x_5337_ = v___x_5334_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
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
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream___boxed(lean_object* v_stream_5340_, lean_object* v_a_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_LeanExport_parseStream(v_stream_5340_);
return v_res_5342_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_String(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
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
res = runtime_initialize_Lean_Data_Json_Parser(builtin);
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
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin);
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
res = initialize_Lean_Data_Json_Parser(builtin);
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

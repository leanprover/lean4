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
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_nbuckets_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_55_ = lean_array_get_size(v_data_54_);
v___x_56_ = lean_unsigned_to_nat(2u);
v_nbuckets_57_ = lean_nat_mul(v___x_55_, v___x_56_);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_box(0);
v___x_60_ = lean_mk_array(v_nbuckets_57_, v___x_59_);
v___x_61_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(v___x_58_, v_data_54_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(lean_object* v_a_62_, lean_object* v_b_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
return v_x_64_;
}
else
{
lean_object* v_key_65_; lean_object* v_value_66_; lean_object* v_tail_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_79_; 
v_key_65_ = lean_ctor_get(v_x_64_, 0);
v_value_66_ = lean_ctor_get(v_x_64_, 1);
v_tail_67_ = lean_ctor_get(v_x_64_, 2);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_79_ == 0)
{
v___x_69_ = v_x_64_;
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_tail_67_);
lean_inc(v_value_66_);
lean_inc(v_key_65_);
lean_dec(v_x_64_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_eq(v_key_65_, v_a_62_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_62_, v_b_63_, v_tail_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 2, v___x_72_);
v___x_74_ = v___x_69_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_key_65_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_value_66_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v_value_66_);
lean_dec(v_key_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v_b_63_);
lean_ctor_set(v___x_69_, 0, v_a_62_);
v___x_77_ = v___x_69_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_62_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_b_63_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v_tail_67_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(lean_object* v_a_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
else
{
lean_object* v_key_83_; lean_object* v_tail_84_; uint8_t v___x_85_; 
v_key_83_ = lean_ctor_get(v_x_81_, 0);
v_tail_84_ = lean_ctor_get(v_x_81_, 2);
v___x_85_ = lean_nat_dec_eq(v_key_83_, v_a_80_);
if (v___x_85_ == 0)
{
v_x_81_ = v_tail_84_;
goto _start;
}
else
{
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_a_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(lean_object* v_m_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_size_94_; lean_object* v_buckets_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_138_; 
v_size_94_ = lean_ctor_get(v_m_91_, 0);
v_buckets_95_ = lean_ctor_get(v_m_91_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_m_91_);
if (v_isSharedCheck_138_ == 0)
{
v___x_97_ = v_m_91_;
v_isShared_98_ = v_isSharedCheck_138_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_buckets_95_);
lean_inc(v_size_94_);
lean_dec(v_m_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_138_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v_fold_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_bkt_112_; uint8_t v___x_113_; 
v___x_99_ = lean_array_get_size(v_buckets_95_);
v___x_100_ = lean_uint64_of_nat(v_a_92_);
v___x_101_ = 32ULL;
v___x_102_ = lean_uint64_shift_right(v___x_100_, v___x_101_);
v_fold_103_ = lean_uint64_xor(v___x_100_, v___x_102_);
v___x_104_ = 16ULL;
v___x_105_ = lean_uint64_shift_right(v_fold_103_, v___x_104_);
v___x_106_ = lean_uint64_xor(v_fold_103_, v___x_105_);
v___x_107_ = lean_uint64_to_usize(v___x_106_);
v___x_108_ = lean_usize_of_nat(v___x_99_);
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_land(v___x_107_, v___x_110_);
v_bkt_112_ = lean_array_uget_borrowed(v_buckets_95_, v___x_111_);
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_92_, v_bkt_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v_size_x27_115_; lean_object* v___x_116_; lean_object* v_buckets_x27_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v_size_x27_115_ = lean_nat_add(v_size_94_, v___x_114_);
lean_dec(v_size_94_);
lean_inc(v_bkt_112_);
v___x_116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_116_, 0, v_a_92_);
lean_ctor_set(v___x_116_, 1, v_b_93_);
lean_ctor_set(v___x_116_, 2, v_bkt_112_);
v_buckets_x27_117_ = lean_array_uset(v_buckets_95_, v___x_111_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(4u);
v___x_119_ = lean_nat_mul(v_size_x27_115_, v___x_118_);
v___x_120_ = lean_unsigned_to_nat(3u);
v___x_121_ = lean_nat_div(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_array_get_size(v_buckets_x27_117_);
v___x_123_ = lean_nat_dec_le(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
if (v___x_123_ == 0)
{
lean_object* v_val_124_; lean_object* v___x_126_; 
v_val_124_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_buckets_x27_117_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_val_124_);
lean_ctor_set(v___x_97_, 0, v_size_x27_115_);
v___x_126_ = v___x_97_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_size_x27_115_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_val_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v___x_129_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_buckets_x27_117_);
lean_ctor_set(v___x_97_, 0, v_size_x27_115_);
v___x_129_ = v___x_97_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_size_x27_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_buckets_x27_117_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v___x_131_; lean_object* v_buckets_x27_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_inc(v_bkt_112_);
v___x_131_ = lean_box(0);
v_buckets_x27_132_ = lean_array_uset(v_buckets_95_, v___x_111_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_92_, v_b_93_, v_bkt_112_);
v___x_134_ = lean_array_uset(v_buckets_x27_132_, v___x_111_, v___x_133_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_134_);
v___x_136_ = v___x_97_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_size_94_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = lean_unsigned_to_nat(16u);
v___x_141_ = lean_mk_array(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__0);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_147_, v___x_146_, v___x_145_);
return v___x_148_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v___x_151_, v___x_150_, v___x_149_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(lean_object* v_x_155_, lean_object* v_stream_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__1);
v___x_159_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__2);
v___x_160_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__3);
v___x_161_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___closed__4));
v___x_162_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_162_, 0, v_stream_156_);
lean_ctor_set(v___x_162_, 1, v___x_159_);
lean_ctor_set(v___x_162_, 2, v___x_160_);
lean_ctor_set(v___x_162_, 3, v___x_158_);
lean_ctor_set(v___x_162_, 4, v___x_158_);
lean_ctor_set(v___x_162_, 5, v___x_158_);
lean_ctor_set(v___x_162_, 6, v___x_161_);
v___x_163_ = lean_apply_2(v_x_155_, v___x_162_, lean_box(0));
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg___boxed(lean_object* v_x_164_, lean_object* v_stream_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_164_, v_stream_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(lean_object* v_00_u03b1_168_, lean_object* v_x_169_, lean_object* v_stream_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v_x_169_, v_stream_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___boxed(lean_object* v_00_u03b1_173_, lean_object* v_x_174_, lean_object* v_stream_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run(v_00_u03b1_173_, v_x_174_, v_stream_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0(lean_object* v_00_u03b2_178_, lean_object* v_m_179_, lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_m_179_, v_a_180_, v_b_181_);
return v___x_182_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(lean_object* v_00_u03b2_183_, lean_object* v_a_184_, lean_object* v_x_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___redArg(v_a_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__0(v_00_u03b2_187_, v_a_188_, v_x_189_);
lean_dec(v_x_189_);
lean_dec(v_a_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1(lean_object* v_00_u03b2_192_, lean_object* v_data_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1___redArg(v_data_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2(lean_object* v_00_u03b2_195_, lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_x_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__2___redArg(v_a_196_, v_b_197_, v_x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_200_, lean_object* v_i_201_, lean_object* v_source_202_, lean_object* v_target_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2___redArg(v_i_201_, v_source_202_, v_target_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0_spec__1_spec__2_spec__3___redArg(v_x_206_, v_x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(lean_object* v_msg_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_211_, 0, v_msg_209_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg___boxed(lean_object* v_msg_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail___redArg(v_msg_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail(lean_object* v_00_u03b1_216_, lean_object* v_msg_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_220_, 0, v_msg_217_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_fail___boxed(lean_object* v_00_u03b1_222_, lean_object* v_msg_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_LeanExport_Parse_0__LeanExport_Parse_fail(v_00_u03b1_222_, v_msg_223_, v_a_224_);
lean_dec_ref(v_a_224_);
return v_res_226_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___f_229_; 
v___x_228_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_229_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_229_, 0, v___x_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName(lean_object* v_nidx_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_nameMap_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_237_; 
v_nameMap_234_ = lean_ctor_get(v_a_232_, 1);
v___f_235_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_236_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_nidx_231_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_236_, v___f_235_, v_nameMap_234_, v_nidx_231_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_nidx_231_);
v_val_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_val_238_);
lean_ctor_set(v___x_242_, 1, v_a_232_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v___x_237_);
lean_dec_ref(v_a_232_);
v___x_247_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_248_ = l_Nat_reprFast(v_nidx_231_);
v___x_249_ = lean_string_append(v___x_247_, v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getName___boxed(lean_object* v_nidx_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getName(v_nidx_252_, v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName(lean_object* v_nidx_256_, lean_object* v_n_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_stream_260_; lean_object* v_nameMap_261_; lean_object* v_levelMap_262_; lean_object* v_exprMap_263_; lean_object* v_recursorRuleMap_264_; lean_object* v_constMap_265_; lean_object* v_constOrder_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_279_; 
v_stream_260_ = lean_ctor_get(v_a_258_, 0);
v_nameMap_261_ = lean_ctor_get(v_a_258_, 1);
v_levelMap_262_ = lean_ctor_get(v_a_258_, 2);
v_exprMap_263_ = lean_ctor_get(v_a_258_, 3);
v_recursorRuleMap_264_ = lean_ctor_get(v_a_258_, 4);
v_constMap_265_ = lean_ctor_get(v_a_258_, 5);
v_constOrder_266_ = lean_ctor_get(v_a_258_, 6);
v_isSharedCheck_279_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_279_ == 0)
{
v___x_268_ = v_a_258_;
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_constOrder_266_);
lean_inc(v_constMap_265_);
lean_inc(v_recursorRuleMap_264_);
lean_inc(v_exprMap_263_);
lean_inc(v_levelMap_262_);
lean_inc(v_nameMap_261_);
lean_inc(v_stream_260_);
lean_dec(v_a_258_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___f_270_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_271_ = lean_box(0);
v___f_272_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_272_, v___f_270_, v_nameMap_261_, v_nidx_256_, v_n_257_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_273_);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_stream_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_levelMap_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_exprMap_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_recursorRuleMap_264_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_constMap_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_constOrder_266_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_271_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addName___boxed(lean_object* v_nidx_280_, lean_object* v_n_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addName(v_nidx_280_, v_n_281_, v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(lean_object* v_uidx_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_levelMap_289_; lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___x_292_; 
v_levelMap_289_ = lean_ctor_get(v_a_287_, 2);
v___f_290_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_291_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_uidx_286_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_291_, v___f_290_, v_levelMap_289_, v_uidx_286_);
if (lean_obj_tag(v___x_292_) == 1)
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_uidx_286_);
v_val_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_val_293_);
lean_ctor_set(v___x_297_, 1, v_a_287_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 0);
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_292_);
lean_dec_ref(v_a_287_);
v___x_302_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_303_ = l_Nat_reprFast(v_uidx_286_);
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___boxed(lean_object* v_uidx_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel(v_uidx_307_, v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(lean_object* v_uidx_311_, lean_object* v_l_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_stream_315_; lean_object* v_nameMap_316_; lean_object* v_levelMap_317_; lean_object* v_exprMap_318_; lean_object* v_recursorRuleMap_319_; lean_object* v_constMap_320_; lean_object* v_constOrder_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_334_; 
v_stream_315_ = lean_ctor_get(v_a_313_, 0);
v_nameMap_316_ = lean_ctor_get(v_a_313_, 1);
v_levelMap_317_ = lean_ctor_get(v_a_313_, 2);
v_exprMap_318_ = lean_ctor_get(v_a_313_, 3);
v_recursorRuleMap_319_ = lean_ctor_get(v_a_313_, 4);
v_constMap_320_ = lean_ctor_get(v_a_313_, 5);
v_constOrder_321_ = lean_ctor_get(v_a_313_, 6);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_334_ == 0)
{
v___x_323_ = v_a_313_;
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_constOrder_321_);
lean_inc(v_constMap_320_);
lean_inc(v_recursorRuleMap_319_);
lean_inc(v_exprMap_318_);
lean_inc(v_levelMap_317_);
lean_inc(v_nameMap_316_);
lean_inc(v_stream_315_);
lean_dec(v_a_313_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___f_325_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_326_ = lean_box(0);
v___f_327_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_327_, v___f_325_, v_levelMap_317_, v_uidx_311_, v_l_312_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 2, v___x_328_);
v___x_330_ = v___x_323_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_stream_315_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_nameMap_316_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_exprMap_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_recursorRuleMap_319_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v_constMap_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_constOrder_321_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_326_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel___boxed(lean_object* v_uidx_335_, lean_object* v_l_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addLevel(v_uidx_335_, v_l_336_, v_a_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(lean_object* v_eidx_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_exprMap_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_exprMap_344_ = lean_ctor_get(v_a_342_, 3);
v___f_345_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_346_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_eidx_341_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_346_, v___f_345_, v_exprMap_344_, v_eidx_341_);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_eidx_341_);
v_val_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_val_348_);
lean_ctor_set(v___x_352_, 1, v_a_342_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 0);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_347_);
lean_dec_ref(v_a_342_);
v___x_357_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_358_ = l_Nat_reprFast(v_eidx_341_);
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___boxed(lean_object* v_eidx_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr(v_eidx_362_, v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(lean_object* v_eidx_366_, lean_object* v_e_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_stream_370_; lean_object* v_nameMap_371_; lean_object* v_levelMap_372_; lean_object* v_exprMap_373_; lean_object* v_recursorRuleMap_374_; lean_object* v_constMap_375_; lean_object* v_constOrder_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_389_; 
v_stream_370_ = lean_ctor_get(v_a_368_, 0);
v_nameMap_371_ = lean_ctor_get(v_a_368_, 1);
v_levelMap_372_ = lean_ctor_get(v_a_368_, 2);
v_exprMap_373_ = lean_ctor_get(v_a_368_, 3);
v_recursorRuleMap_374_ = lean_ctor_get(v_a_368_, 4);
v_constMap_375_ = lean_ctor_get(v_a_368_, 5);
v_constOrder_376_ = lean_ctor_get(v_a_368_, 6);
v_isSharedCheck_389_ = !lean_is_exclusive(v_a_368_);
if (v_isSharedCheck_389_ == 0)
{
v___x_378_ = v_a_368_;
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_constOrder_376_);
lean_inc(v_constMap_375_);
lean_inc(v_recursorRuleMap_374_);
lean_inc(v_exprMap_373_);
lean_inc(v_levelMap_372_);
lean_inc(v_nameMap_371_);
lean_inc(v_stream_370_);
lean_dec(v_a_368_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___f_380_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_381_ = lean_box(0);
v___f_382_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_382_, v___f_380_, v_exprMap_373_, v_eidx_366_, v_e_367_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 3, v___x_383_);
v___x_385_ = v___x_378_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_stream_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_nameMap_371_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_levelMap_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_recursorRuleMap_374_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_constMap_375_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_constOrder_376_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_381_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr___boxed(lean_object* v_eidx_390_, lean_object* v_e_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addExpr(v_eidx_390_, v_e_391_, v_a_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(lean_object* v_ridx_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_recursorRuleMap_399_; lean_object* v___f_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v_recursorRuleMap_399_ = lean_ctor_get(v_a_397_, 4);
v___f_400_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___f_401_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
lean_inc(v_ridx_396_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_401_, v___f_400_, v_recursorRuleMap_399_, v_ridx_396_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_ridx_396_);
v_val_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_val_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_val_403_);
lean_ctor_set(v___x_407_, 1, v_a_397_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_402_);
lean_dec_ref(v_a_397_);
v___x_412_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___closed__0));
v___x_413_ = l_Nat_reprFast(v_ridx_396_);
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
lean_dec_ref(v___x_413_);
v___x_415_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule___boxed(lean_object* v_ridx_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getRecursorRule(v_ridx_417_, v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(lean_object* v_ridx_421_, lean_object* v_r_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_stream_425_; lean_object* v_nameMap_426_; lean_object* v_levelMap_427_; lean_object* v_exprMap_428_; lean_object* v_recursorRuleMap_429_; lean_object* v_constMap_430_; lean_object* v_constOrder_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_444_; 
v_stream_425_ = lean_ctor_get(v_a_423_, 0);
v_nameMap_426_ = lean_ctor_get(v_a_423_, 1);
v_levelMap_427_ = lean_ctor_get(v_a_423_, 2);
v_exprMap_428_ = lean_ctor_get(v_a_423_, 3);
v_recursorRuleMap_429_ = lean_ctor_get(v_a_423_, 4);
v_constMap_430_ = lean_ctor_get(v_a_423_, 5);
v_constOrder_431_ = lean_ctor_get(v_a_423_, 6);
v_isSharedCheck_444_ = !lean_is_exclusive(v_a_423_);
if (v_isSharedCheck_444_ == 0)
{
v___x_433_ = v_a_423_;
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_constOrder_431_);
lean_inc(v_constMap_430_);
lean_inc(v_recursorRuleMap_429_);
lean_inc(v_exprMap_428_);
lean_inc(v_levelMap_427_);
lean_inc(v_nameMap_426_);
lean_inc(v_stream_425_);
lean_dec(v_a_423_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___f_435_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__0));
v___x_436_ = lean_box(0);
v___f_437_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1, &l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__1);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_437_, v___f_435_, v_recursorRuleMap_429_, v_ridx_421_, v_r_422_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v___x_438_);
v___x_440_ = v___x_433_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_stream_425_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_nameMap_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_levelMap_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_exprMap_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_constMap_430_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_constOrder_431_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_436_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule___boxed(lean_object* v_ridx_445_, lean_object* v_r_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addRecursorRule(v_ridx_445_, v_r_446_, v_a_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(lean_object* v_name_453_, lean_object* v_d_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_stream_457_; lean_object* v_nameMap_458_; lean_object* v_levelMap_459_; lean_object* v_exprMap_460_; lean_object* v_recursorRuleMap_461_; lean_object* v_constMap_462_; lean_object* v_constOrder_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_483_; 
v_stream_457_ = lean_ctor_get(v_a_455_, 0);
v_nameMap_458_ = lean_ctor_get(v_a_455_, 1);
v_levelMap_459_ = lean_ctor_get(v_a_455_, 2);
v_exprMap_460_ = lean_ctor_get(v_a_455_, 3);
v_recursorRuleMap_461_ = lean_ctor_get(v_a_455_, 4);
v_constMap_462_ = lean_ctor_get(v_a_455_, 5);
v_constOrder_463_ = lean_ctor_get(v_a_455_, 6);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_483_ == 0)
{
v___x_465_ = v_a_455_;
v_isShared_466_ = v_isSharedCheck_483_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_constOrder_463_);
lean_inc(v_constMap_462_);
lean_inc(v_recursorRuleMap_461_);
lean_inc(v_exprMap_460_);
lean_inc(v_levelMap_459_);
lean_inc(v_nameMap_458_);
lean_inc(v_stream_457_);
lean_dec(v_a_455_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_483_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_467_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__0));
v___x_468_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__1));
lean_inc(v_name_453_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_467_, v___x_468_, v_constMap_462_, v_name_453_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_470_ = lean_box(0);
lean_inc(v_name_453_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_467_, v___x_468_, v_constMap_462_, v_name_453_, v_d_454_);
v___x_472_ = lean_array_push(v_constOrder_463_, v_name_453_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 6, v___x_472_);
lean_ctor_set(v___x_465_, 5, v___x_471_);
v___x_474_ = v___x_465_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_stream_457_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_nameMap_458_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_levelMap_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_exprMap_460_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_recursorRuleMap_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v___x_472_);
v___x_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_470_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_del_object(v___x_465_);
lean_dec_ref(v_constOrder_463_);
lean_dec_ref(v_constMap_462_);
lean_dec_ref(v_recursorRuleMap_461_);
lean_dec_ref(v_exprMap_460_);
lean_dec_ref(v_levelMap_459_);
lean_dec_ref(v_nameMap_458_);
lean_dec_ref(v_stream_457_);
lean_dec_ref(v_d_454_);
v___x_478_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_479_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_453_, v___x_469_);
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___boxed(lean_object* v_name_484_, lean_object* v_d_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_LeanExport_Parse_0__LeanExport_Parse_addConst(v_name_484_, v_d_485_, v_a_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(lean_object* v_line_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
v___x_500_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_499_, v_line_493_);
if (lean_obj_tag(v___x_500_) == 1)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
if (lean_obj_tag(v_a_501_) == 5)
{
lean_object* v_kvPairs_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_kvPairs_502_ = lean_ctor_get(v_a_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_a_501_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_kvPairs_502_);
lean_dec(v_a_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_kvPairs_502_);
lean_ctor_set(v___x_506_, 1, v_a_494_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_dec(v_a_501_);
lean_dec_ref(v_a_494_);
goto v___jp_496_;
}
}
else
{
lean_dec_ref(v___x_500_);
lean_dec_ref(v_a_494_);
goto v___jp_496_;
}
v___jp_496_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1));
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___boxed(lean_object* v_line_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj(v_line_511_, v_a_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_box(0);
return v___x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_value_519_; lean_object* v_tail_520_; uint8_t v___x_521_; 
v_key_518_ = lean_ctor_get(v_x_516_, 0);
v_value_519_ = lean_ctor_get(v_x_516_, 1);
v_tail_520_ = lean_ctor_get(v_x_516_, 2);
v___x_521_ = lean_nat_dec_eq(v_key_518_, v_a_515_);
if (v___x_521_ == 0)
{
v_x_516_ = v_tail_520_;
goto _start;
}
else
{
lean_object* v___x_523_; 
lean_inc(v_value_519_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_value_519_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg___boxed(lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_524_, v_x_525_);
lean_dec(v_x_525_);
lean_dec(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_buckets_529_; lean_object* v___x_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v_fold_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_buckets_529_ = lean_ctor_get(v_m_527_, 1);
v___x_530_ = lean_array_get_size(v_buckets_529_);
v___x_531_ = lean_uint64_of_nat(v_a_528_);
v___x_532_ = 32ULL;
v___x_533_ = lean_uint64_shift_right(v___x_531_, v___x_532_);
v_fold_534_ = lean_uint64_xor(v___x_531_, v___x_533_);
v___x_535_ = 16ULL;
v___x_536_ = lean_uint64_shift_right(v_fold_534_, v___x_535_);
v___x_537_ = lean_uint64_xor(v_fold_534_, v___x_536_);
v___x_538_ = lean_uint64_to_usize(v___x_537_);
v___x_539_ = lean_usize_of_nat(v___x_530_);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_sub(v___x_539_, v___x_540_);
v___x_542_ = lean_usize_land(v___x_538_, v___x_541_);
v___x_543_ = lean_array_uget_borrowed(v_buckets_529_, v___x_542_);
v___x_544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_528_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg___boxed(lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_m_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(lean_object* v_t_548_, lean_object* v_k_549_){
_start:
{
if (lean_obj_tag(v_t_548_) == 0)
{
lean_object* v_k_550_; lean_object* v_v_551_; lean_object* v_l_552_; lean_object* v_r_553_; uint8_t v___x_554_; 
v_k_550_ = lean_ctor_get(v_t_548_, 1);
v_v_551_ = lean_ctor_get(v_t_548_, 2);
v_l_552_ = lean_ctor_get(v_t_548_, 3);
v_r_553_ = lean_ctor_get(v_t_548_, 4);
v___x_554_ = lean_string_compare(v_k_549_, v_k_550_);
switch(v___x_554_)
{
case 0:
{
v_t_548_ = v_l_552_;
goto _start;
}
case 1:
{
lean_object* v___x_556_; 
lean_inc(v_v_551_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_v_551_);
return v___x_556_;
}
default: 
{
v_t_548_ = v_r_553_;
goto _start;
}
}
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg___boxed(lean_object* v_t_559_, lean_object* v_k_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_559_, v_k_560_);
lean_dec_ref(v_k_560_);
lean_dec(v_t_559_);
return v_res_561_;
}
}
static lean_object* _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3(void){
_start:
{
lean_object* v_natZero_566_; lean_object* v_intZero_567_; 
v_natZero_566_ = lean_unsigned_to_nat(0u);
v_intZero_567_ = lean_nat_to_int(v_natZero_566_);
return v_intZero_567_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(lean_object* v_json_569_, lean_object* v_a_570_){
_start:
{
if (lean_obj_tag(v_json_569_) == 5)
{
lean_object* v_kvPairs_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_kvPairs_578_ = lean_ctor_get(v_json_569_, 0);
v___x_579_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_578_, v___x_579_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
if (lean_obj_tag(v_val_581_) == 2)
{
lean_object* v_n_582_; lean_object* v_mantissa_583_; lean_object* v_exponent_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_628_; 
v_n_582_ = lean_ctor_get(v_val_581_, 0);
lean_inc_ref(v_n_582_);
lean_dec_ref_known(v_val_581_, 1);
v_mantissa_583_ = lean_ctor_get(v_n_582_, 0);
v_exponent_584_ = lean_ctor_get(v_n_582_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_n_582_);
if (v_isSharedCheck_628_ == 0)
{
v___x_586_ = v_n_582_;
v_isShared_587_ = v_isSharedCheck_628_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_exponent_584_);
lean_inc(v_mantissa_583_);
lean_dec(v_n_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_628_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_natZero_588_; lean_object* v_intZero_589_; uint8_t v_isNeg_590_; 
v_natZero_588_ = lean_unsigned_to_nat(0u);
v_intZero_589_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_590_ = lean_int_dec_lt(v_mantissa_583_, v_intZero_589_);
if (v_isNeg_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_eq(v_exponent_584_, v_natZero_588_);
lean_dec(v_exponent_584_);
if (v___x_591_ == 0)
{
lean_del_object(v___x_586_);
lean_dec(v_mantissa_583_);
lean_dec_ref(v_a_570_);
goto v___jp_572_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_578_, v___x_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_627_; 
v_val_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_627_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_627_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_627_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
if (lean_obj_tag(v_val_594_) == 3)
{
lean_object* v_s_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_626_; 
v_s_598_ = lean_ctor_get(v_val_594_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_val_594_);
if (v_isSharedCheck_626_ == 0)
{
v___x_600_ = v_val_594_;
v_isShared_601_ = v_isSharedCheck_626_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_s_598_);
lean_dec(v_val_594_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_626_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_nameMap_602_; lean_object* v_a_603_; lean_object* v___x_604_; 
v_nameMap_602_ = lean_ctor_get(v_a_570_, 1);
v_a_603_ = lean_nat_abs(v_mantissa_583_);
lean_dec(v_mantissa_583_);
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_602_, v_a_603_);
if (lean_obj_tag(v___x_604_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_603_);
lean_del_object(v___x_600_);
lean_del_object(v___x_596_);
v_val_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_616_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = l_Lean_Name_str___override(v_val_605_, v_s_598_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_a_570_);
lean_ctor_set(v___x_586_, 0, v___x_609_);
v___x_611_ = v___x_586_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_570_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 0);
lean_ctor_set(v___x_607_, 0, v___x_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v___x_604_);
lean_dec_ref(v_s_598_);
lean_del_object(v___x_586_);
lean_dec_ref(v_a_570_);
v___x_617_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_618_ = l_Nat_reprFast(v_a_603_);
v___x_619_ = lean_string_append(v___x_617_, v___x_618_);
lean_dec_ref(v___x_618_);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 18);
lean_ctor_set(v___x_600_, 0, v___x_619_);
v___x_621_ = v___x_600_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_621_);
v___x_623_ = v___x_596_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
else
{
lean_del_object(v___x_596_);
lean_dec(v_val_594_);
lean_del_object(v___x_586_);
lean_dec(v_mantissa_583_);
lean_dec_ref(v_a_570_);
goto v___jp_575_;
}
}
}
else
{
lean_dec(v___x_593_);
lean_del_object(v___x_586_);
lean_dec(v_mantissa_583_);
lean_dec_ref(v_a_570_);
goto v___jp_575_;
}
}
}
else
{
lean_del_object(v___x_586_);
lean_dec(v_exponent_584_);
lean_dec(v_mantissa_583_);
lean_dec_ref(v_a_570_);
goto v___jp_572_;
}
}
}
else
{
lean_dec(v_val_581_);
lean_dec_ref(v_a_570_);
goto v___jp_572_;
}
}
else
{
lean_dec(v___x_580_);
lean_dec_ref(v_a_570_);
goto v___jp_572_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_a_570_);
v___x_629_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
v___jp_572_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
v___jp_575_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___boxed(lean_object* v_json_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_json_631_, v_a_632_);
lean_dec(v_json_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(lean_object* v_00_u03b4_635_, lean_object* v_t_636_, lean_object* v_k_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_t_636_, v_k_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___boxed(lean_object* v_00_u03b4_639_, lean_object* v_t_640_, lean_object* v_k_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0(v_00_u03b4_639_, v_t_640_, v_k_641_);
lean_dec_ref(v_k_641_);
lean_dec(v_t_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_m_644_, v_a_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___boxed(lean_object* v_00_u03b2_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1(v_00_u03b2_647_, v_m_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_m_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(lean_object* v_00_u03b2_651_, lean_object* v_a_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___redArg(v_a_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1___boxed(lean_object* v_00_u03b2_655_, lean_object* v_a_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1_spec__1(v_00_u03b2_655_, v_a_656_, v_x_657_);
lean_dec(v_x_657_);
lean_dec(v_a_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(lean_object* v_json_663_, lean_object* v_a_664_){
_start:
{
if (lean_obj_tag(v_json_663_) == 5)
{
lean_object* v_kvPairs_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_kvPairs_672_ = lean_ctor_get(v_json_663_, 0);
v___x_673_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__2));
v___x_674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_672_, v___x_673_);
if (lean_obj_tag(v___x_674_) == 1)
{
lean_object* v_val_675_; 
v_val_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v___x_674_, 1);
if (lean_obj_tag(v_val_675_) == 2)
{
lean_object* v_n_676_; lean_object* v_mantissa_677_; lean_object* v_exponent_678_; lean_object* v_natZero_679_; lean_object* v_intZero_680_; uint8_t v_isNeg_681_; 
v_n_676_ = lean_ctor_get(v_val_675_, 0);
lean_inc_ref(v_n_676_);
lean_dec_ref_known(v_val_675_, 1);
v_mantissa_677_ = lean_ctor_get(v_n_676_, 0);
lean_inc(v_mantissa_677_);
v_exponent_678_ = lean_ctor_get(v_n_676_, 1);
lean_inc(v_exponent_678_);
lean_dec_ref(v_n_676_);
v_natZero_679_ = lean_unsigned_to_nat(0u);
v_intZero_680_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_681_ = lean_int_dec_lt(v_mantissa_677_, v_intZero_680_);
if (v_isNeg_681_ == 0)
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_eq(v_exponent_678_, v_natZero_679_);
lean_dec(v_exponent_678_);
if (v___x_682_ == 0)
{
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_666_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__2));
v___x_684_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_672_, v___x_683_);
if (lean_obj_tag(v___x_684_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_727_; 
v_val_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_727_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_727_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_727_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
if (lean_obj_tag(v_val_685_) == 2)
{
lean_object* v_n_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_726_; 
v_n_689_ = lean_ctor_get(v_val_685_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_val_685_);
if (v_isSharedCheck_726_ == 0)
{
v___x_691_ = v_val_685_;
v_isShared_692_ = v_isSharedCheck_726_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_n_689_);
lean_dec(v_val_685_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_726_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_mantissa_693_; lean_object* v_exponent_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_725_; 
v_mantissa_693_ = lean_ctor_get(v_n_689_, 0);
v_exponent_694_ = lean_ctor_get(v_n_689_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_n_689_);
if (v_isSharedCheck_725_ == 0)
{
v___x_696_ = v_n_689_;
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_exponent_694_);
lean_inc(v_mantissa_693_);
lean_dec(v_n_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v_isNeg_698_; 
v_isNeg_698_ = lean_int_dec_lt(v_mantissa_693_, v_intZero_680_);
if (v_isNeg_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_eq(v_exponent_694_, v_natZero_679_);
lean_dec(v_exponent_694_);
if (v___x_699_ == 0)
{
lean_del_object(v___x_696_);
lean_dec(v_mantissa_693_);
lean_del_object(v___x_691_);
lean_del_object(v___x_687_);
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_669_;
}
else
{
lean_object* v_nameMap_700_; lean_object* v_a_701_; lean_object* v___x_702_; 
v_nameMap_700_ = lean_ctor_get(v_a_664_, 1);
v_a_701_ = lean_nat_abs(v_mantissa_677_);
lean_dec(v_mantissa_677_);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_700_, v_a_701_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_701_);
lean_del_object(v___x_691_);
lean_del_object(v___x_687_);
v_val_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_715_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_715_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_715_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v_a_707_ = lean_nat_abs(v_mantissa_693_);
lean_dec(v_mantissa_693_);
v___x_708_ = l_Lean_Name_num___override(v_val_703_, v_a_707_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_a_664_);
lean_ctor_set(v___x_696_, 0, v___x_708_);
v___x_710_ = v___x_696_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_a_664_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 0);
lean_ctor_set(v___x_705_, 0, v___x_710_);
v___x_712_ = v___x_705_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec(v___x_702_);
lean_del_object(v___x_696_);
lean_dec(v_mantissa_693_);
lean_dec_ref(v_a_664_);
v___x_716_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_717_ = l_Nat_reprFast(v_a_701_);
v___x_718_ = lean_string_append(v___x_716_, v___x_717_);
lean_dec_ref(v___x_717_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 18);
lean_ctor_set(v___x_691_, 0, v___x_718_);
v___x_720_ = v___x_691_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_720_);
v___x_722_ = v___x_687_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
else
{
lean_del_object(v___x_696_);
lean_dec(v_exponent_694_);
lean_dec(v_mantissa_693_);
lean_del_object(v___x_691_);
lean_del_object(v___x_687_);
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_669_;
}
}
}
}
else
{
lean_del_object(v___x_687_);
lean_dec(v_val_685_);
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_669_;
}
}
}
else
{
lean_dec(v___x_684_);
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_669_;
}
}
}
else
{
lean_dec(v_exponent_678_);
lean_dec(v_mantissa_677_);
lean_dec_ref(v_a_664_);
goto v___jp_666_;
}
}
else
{
lean_dec(v_val_675_);
lean_dec_ref(v_a_664_);
goto v___jp_666_;
}
}
else
{
lean_dec(v___x_674_);
lean_dec_ref(v_a_664_);
goto v___jp_666_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_a_664_);
v___x_728_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
v___jp_666_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__1));
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___closed__1));
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum___boxed(lean_object* v_json_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_json_730_, v_a_731_);
lean_dec(v_json_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(lean_object* v_json_737_, lean_object* v_a_738_){
_start:
{
if (lean_obj_tag(v_json_737_) == 2)
{
lean_object* v_n_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_779_; 
v_n_743_ = lean_ctor_get(v_json_737_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_json_737_);
if (v_isSharedCheck_779_ == 0)
{
v___x_745_ = v_json_737_;
v_isShared_746_ = v_isSharedCheck_779_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_n_743_);
lean_dec(v_json_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_779_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_mantissa_747_; lean_object* v_exponent_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_778_; 
v_mantissa_747_ = lean_ctor_get(v_n_743_, 0);
v_exponent_748_ = lean_ctor_get(v_n_743_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_n_743_);
if (v_isSharedCheck_778_ == 0)
{
v___x_750_ = v_n_743_;
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_exponent_748_);
lean_inc(v_mantissa_747_);
lean_dec(v_n_743_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_natZero_752_; lean_object* v_intZero_753_; uint8_t v_isNeg_754_; 
v_natZero_752_ = lean_unsigned_to_nat(0u);
v_intZero_753_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_754_ = lean_int_dec_lt(v_mantissa_747_, v_intZero_753_);
if (v_isNeg_754_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_eq(v_exponent_748_, v_natZero_752_);
lean_dec(v_exponent_748_);
if (v___x_755_ == 0)
{
lean_del_object(v___x_750_);
lean_dec(v_mantissa_747_);
lean_del_object(v___x_745_);
lean_dec_ref(v_a_738_);
goto v___jp_740_;
}
else
{
lean_object* v_levelMap_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v_levelMap_756_ = lean_ctor_get(v_a_738_, 2);
v_a_757_ = lean_nat_abs(v_mantissa_747_);
lean_dec(v_mantissa_747_);
v___x_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_756_, v_a_757_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_757_);
lean_del_object(v___x_745_);
v_val_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_val_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = l_Lean_Level_succ___override(v_val_759_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v_a_738_);
lean_ctor_set(v___x_750_, 0, v___x_763_);
v___x_765_ = v___x_750_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_738_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
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
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v___x_758_);
lean_del_object(v___x_750_);
lean_dec_ref(v_a_738_);
v___x_771_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_772_ = l_Nat_reprFast(v_a_757_);
v___x_773_ = lean_string_append(v___x_771_, v___x_772_);
lean_dec_ref(v___x_772_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 18);
lean_ctor_set(v___x_745_, 0, v___x_773_);
v___x_775_ = v___x_745_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
}
else
{
lean_del_object(v___x_750_);
lean_dec(v_exponent_748_);
lean_dec(v_mantissa_747_);
lean_del_object(v___x_745_);
lean_dec_ref(v_a_738_);
goto v___jp_740_;
}
}
}
}
else
{
lean_dec_ref(v_a_738_);
lean_dec(v_json_737_);
goto v___jp_740_;
}
v___jp_740_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___closed__1));
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc___boxed(lean_object* v_json_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_json_780_, v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(lean_object* v_json_787_, lean_object* v_a_788_){
_start:
{
if (lean_obj_tag(v_json_787_) == 4)
{
lean_object* v_elems_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_elems_793_ = lean_ctor_get(v_json_787_, 0);
v___x_794_ = lean_array_get_size(v_elems_793_);
v___x_795_ = lean_unsigned_to_nat(2u);
v___x_796_ = lean_nat_dec_eq(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_array_fget(v_elems_793_, v___x_797_);
if (lean_obj_tag(v___x_798_) == 2)
{
lean_object* v_n_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_863_; 
v_n_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_863_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_863_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_n_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_863_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_mantissa_803_; lean_object* v_exponent_804_; lean_object* v_intZero_805_; uint8_t v_isNeg_806_; 
v_mantissa_803_ = lean_ctor_get(v_n_799_, 0);
lean_inc(v_mantissa_803_);
v_exponent_804_ = lean_ctor_get(v_n_799_, 1);
lean_inc(v_exponent_804_);
lean_dec_ref(v_n_799_);
v_intZero_805_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_806_ = lean_int_dec_lt(v_mantissa_803_, v_intZero_805_);
if (v_isNeg_806_ == 0)
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_eq(v_exponent_804_, v___x_797_);
lean_dec(v_exponent_804_);
if (v___x_807_ == 0)
{
lean_dec(v_mantissa_803_);
lean_del_object(v___x_801_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_array_fget(v_elems_793_, v___x_808_);
if (lean_obj_tag(v___x_809_) == 2)
{
lean_object* v_n_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_862_; 
v_n_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_862_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_862_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_n_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_862_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_mantissa_814_; lean_object* v_exponent_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_861_; 
v_mantissa_814_ = lean_ctor_get(v_n_810_, 0);
v_exponent_815_ = lean_ctor_get(v_n_810_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_n_810_);
if (v_isSharedCheck_861_ == 0)
{
v___x_817_ = v_n_810_;
v_isShared_818_ = v_isSharedCheck_861_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_exponent_815_);
lean_inc(v_mantissa_814_);
lean_dec(v_n_810_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_861_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v_isNeg_819_; 
v_isNeg_819_ = lean_int_dec_lt(v_mantissa_814_, v_intZero_805_);
if (v_isNeg_819_ == 0)
{
uint8_t v___x_820_; 
v___x_820_ = lean_nat_dec_eq(v_exponent_815_, v___x_797_);
lean_dec(v_exponent_815_);
if (v___x_820_ == 0)
{
lean_del_object(v___x_817_);
lean_dec(v_mantissa_814_);
lean_del_object(v___x_812_);
lean_dec(v_mantissa_803_);
lean_del_object(v___x_801_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
else
{
lean_object* v_levelMap_821_; lean_object* v_a_822_; lean_object* v___x_823_; 
v_levelMap_821_ = lean_ctor_get(v_a_788_, 2);
v_a_822_ = lean_nat_abs(v_mantissa_803_);
lean_dec(v_mantissa_803_);
v___x_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_821_, v_a_822_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_a_822_);
lean_del_object(v___x_801_);
v_val_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_851_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_851_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_851_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_nat_abs(v_mantissa_814_);
lean_dec(v_mantissa_814_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_821_, v_a_828_);
if (lean_obj_tag(v___x_829_) == 1)
{
lean_object* v_val_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_828_);
lean_del_object(v___x_826_);
lean_del_object(v___x_812_);
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
v___x_834_ = l_Lean_Level_max___override(v_val_824_, v_val_830_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_a_788_);
lean_ctor_set(v___x_817_, 0, v___x_834_);
v___x_836_ = v___x_817_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_788_);
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
lean_dec(v_val_824_);
lean_del_object(v___x_817_);
lean_dec_ref(v_a_788_);
v___x_842_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_843_ = l_Nat_reprFast(v_a_828_);
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
lean_dec_ref(v___x_843_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 18);
lean_ctor_set(v___x_826_, 0, v___x_844_);
v___x_846_ = v___x_826_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 0, v___x_846_);
v___x_848_ = v___x_812_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v___x_823_);
lean_del_object(v___x_817_);
lean_dec(v_mantissa_814_);
lean_dec_ref(v_a_788_);
v___x_852_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_853_ = l_Nat_reprFast(v_a_822_);
v___x_854_ = lean_string_append(v___x_852_, v___x_853_);
lean_dec_ref(v___x_853_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 18);
lean_ctor_set(v___x_812_, 0, v___x_854_);
v___x_856_ = v___x_812_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v___x_856_);
v___x_858_ = v___x_801_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_del_object(v___x_817_);
lean_dec(v_exponent_815_);
lean_dec(v_mantissa_814_);
lean_del_object(v___x_812_);
lean_dec(v_mantissa_803_);
lean_del_object(v___x_801_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
}
}
}
else
{
lean_dec(v___x_809_);
lean_dec(v_mantissa_803_);
lean_del_object(v___x_801_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
}
}
else
{
lean_dec(v_exponent_804_);
lean_dec(v_mantissa_803_);
lean_del_object(v___x_801_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
}
}
else
{
lean_dec(v___x_798_);
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
}
}
else
{
lean_dec_ref(v_a_788_);
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___closed__1));
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax___boxed(lean_object* v_json_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_json_864_, v_a_865_);
lean_dec(v_json_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(lean_object* v_json_871_, lean_object* v_a_872_){
_start:
{
if (lean_obj_tag(v_json_871_) == 4)
{
lean_object* v_elems_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_elems_877_ = lean_ctor_get(v_json_871_, 0);
v___x_878_ = lean_array_get_size(v_elems_877_);
v___x_879_ = lean_unsigned_to_nat(2u);
v___x_880_ = lean_nat_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_array_fget(v_elems_877_, v___x_881_);
if (lean_obj_tag(v___x_882_) == 2)
{
lean_object* v_n_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_947_; 
v_n_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_947_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_947_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_n_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_947_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_mantissa_887_; lean_object* v_exponent_888_; lean_object* v_intZero_889_; uint8_t v_isNeg_890_; 
v_mantissa_887_ = lean_ctor_get(v_n_883_, 0);
lean_inc(v_mantissa_887_);
v_exponent_888_ = lean_ctor_get(v_n_883_, 1);
lean_inc(v_exponent_888_);
lean_dec_ref(v_n_883_);
v_intZero_889_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_890_ = lean_int_dec_lt(v_mantissa_887_, v_intZero_889_);
if (v_isNeg_890_ == 0)
{
uint8_t v___x_891_; 
v___x_891_ = lean_nat_dec_eq(v_exponent_888_, v___x_881_);
lean_dec(v_exponent_888_);
if (v___x_891_ == 0)
{
lean_dec(v_mantissa_887_);
lean_del_object(v___x_885_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_array_fget(v_elems_877_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 2)
{
lean_object* v_n_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_946_; 
v_n_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_946_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_946_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_n_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_946_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_mantissa_898_; lean_object* v_exponent_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_945_; 
v_mantissa_898_ = lean_ctor_get(v_n_894_, 0);
v_exponent_899_ = lean_ctor_get(v_n_894_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_n_894_);
if (v_isSharedCheck_945_ == 0)
{
v___x_901_ = v_n_894_;
v_isShared_902_ = v_isSharedCheck_945_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_exponent_899_);
lean_inc(v_mantissa_898_);
lean_dec(v_n_894_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_945_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
uint8_t v_isNeg_903_; 
v_isNeg_903_ = lean_int_dec_lt(v_mantissa_898_, v_intZero_889_);
if (v_isNeg_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_eq(v_exponent_899_, v___x_881_);
lean_dec(v_exponent_899_);
if (v___x_904_ == 0)
{
lean_del_object(v___x_901_);
lean_dec(v_mantissa_898_);
lean_del_object(v___x_896_);
lean_dec(v_mantissa_887_);
lean_del_object(v___x_885_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
else
{
lean_object* v_levelMap_905_; lean_object* v_a_906_; lean_object* v___x_907_; 
v_levelMap_905_ = lean_ctor_get(v_a_872_, 2);
v_a_906_ = lean_nat_abs(v_mantissa_887_);
lean_dec(v_mantissa_887_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_905_, v_a_906_);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_906_);
lean_del_object(v___x_885_);
v_val_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_935_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_935_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_935_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_nat_abs(v_mantissa_898_);
lean_dec(v_mantissa_898_);
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_905_, v_a_912_);
if (lean_obj_tag(v___x_913_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_912_);
lean_del_object(v___x_910_);
lean_del_object(v___x_896_);
v_val_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_val_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = l_Lean_Level_imax___override(v_val_908_, v_val_914_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_a_872_);
lean_ctor_set(v___x_901_, 0, v___x_918_);
v___x_920_ = v___x_901_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_872_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 0);
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v___x_913_);
lean_dec(v_val_908_);
lean_del_object(v___x_901_);
lean_dec_ref(v_a_872_);
v___x_926_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_927_ = l_Nat_reprFast(v_a_912_);
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
lean_dec_ref(v___x_927_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 18);
lean_ctor_set(v___x_910_, 0, v___x_928_);
v___x_930_ = v___x_910_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 1);
lean_ctor_set(v___x_896_, 0, v___x_930_);
v___x_932_ = v___x_896_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec(v___x_907_);
lean_del_object(v___x_901_);
lean_dec(v_mantissa_898_);
lean_dec_ref(v_a_872_);
v___x_936_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_937_ = l_Nat_reprFast(v_a_906_);
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
lean_dec_ref(v___x_937_);
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 18);
lean_ctor_set(v___x_896_, 0, v___x_938_);
v___x_940_ = v___x_896_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 1);
lean_ctor_set(v___x_885_, 0, v___x_940_);
v___x_942_ = v___x_885_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
lean_del_object(v___x_901_);
lean_dec(v_exponent_899_);
lean_dec(v_mantissa_898_);
lean_del_object(v___x_896_);
lean_dec(v_mantissa_887_);
lean_del_object(v___x_885_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
}
}
}
else
{
lean_dec(v___x_893_);
lean_dec(v_mantissa_887_);
lean_del_object(v___x_885_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
}
}
else
{
lean_dec(v_exponent_888_);
lean_dec(v_mantissa_887_);
lean_del_object(v___x_885_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
}
}
else
{
lean_dec(v___x_882_);
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
}
}
else
{
lean_dec_ref(v_a_872_);
goto v___jp_874_;
}
v___jp_874_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___closed__1));
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax___boxed(lean_object* v_json_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_json_948_, v_a_949_);
lean_dec(v_json_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(lean_object* v_json_955_, lean_object* v_a_956_){
_start:
{
if (lean_obj_tag(v_json_955_) == 2)
{
lean_object* v_n_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_997_; 
v_n_961_ = lean_ctor_get(v_json_955_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_json_955_);
if (v_isSharedCheck_997_ == 0)
{
v___x_963_ = v_json_955_;
v_isShared_964_ = v_isSharedCheck_997_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_n_961_);
lean_dec(v_json_955_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_997_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_mantissa_965_; lean_object* v_exponent_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_996_; 
v_mantissa_965_ = lean_ctor_get(v_n_961_, 0);
v_exponent_966_ = lean_ctor_get(v_n_961_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_n_961_);
if (v_isSharedCheck_996_ == 0)
{
v___x_968_ = v_n_961_;
v_isShared_969_ = v_isSharedCheck_996_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_exponent_966_);
lean_inc(v_mantissa_965_);
lean_dec(v_n_961_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_996_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_natZero_970_; lean_object* v_intZero_971_; uint8_t v_isNeg_972_; 
v_natZero_970_ = lean_unsigned_to_nat(0u);
v_intZero_971_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_972_ = lean_int_dec_lt(v_mantissa_965_, v_intZero_971_);
if (v_isNeg_972_ == 0)
{
uint8_t v___x_973_; 
v___x_973_ = lean_nat_dec_eq(v_exponent_966_, v_natZero_970_);
lean_dec(v_exponent_966_);
if (v___x_973_ == 0)
{
lean_del_object(v___x_968_);
lean_dec(v_mantissa_965_);
lean_del_object(v___x_963_);
lean_dec_ref(v_a_956_);
goto v___jp_958_;
}
else
{
lean_object* v_nameMap_974_; lean_object* v_a_975_; lean_object* v___x_976_; 
v_nameMap_974_ = lean_ctor_get(v_a_956_, 1);
v_a_975_ = lean_nat_abs(v_mantissa_965_);
lean_dec(v_mantissa_965_);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_974_, v_a_975_);
if (lean_obj_tag(v___x_976_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_975_);
lean_del_object(v___x_963_);
v_val_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_988_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = l_Lean_Level_param___override(v_val_977_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_a_956_);
lean_ctor_set(v___x_968_, 0, v___x_981_);
v___x_983_ = v___x_968_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_956_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
lean_ctor_set(v___x_979_, 0, v___x_983_);
v___x_985_ = v___x_979_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v___x_976_);
lean_del_object(v___x_968_);
lean_dec_ref(v_a_956_);
v___x_989_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_990_ = l_Nat_reprFast(v_a_975_);
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
lean_dec_ref(v___x_990_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 18);
lean_ctor_set(v___x_963_, 0, v___x_991_);
v___x_993_ = v___x_963_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
}
else
{
lean_del_object(v___x_968_);
lean_dec(v_exponent_966_);
lean_dec(v_mantissa_965_);
lean_del_object(v___x_963_);
lean_dec_ref(v_a_956_);
goto v___jp_958_;
}
}
}
}
else
{
lean_dec_ref(v_a_956_);
lean_dec(v_json_955_);
goto v___jp_958_;
}
v___jp_958_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___closed__1));
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam___boxed(lean_object* v_json_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_json_998_, v_a_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(lean_object* v_json_1005_, lean_object* v_a_1006_){
_start:
{
if (lean_obj_tag(v_json_1005_) == 2)
{
lean_object* v_n_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1033_; 
v_n_1011_ = lean_ctor_get(v_json_1005_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_json_1005_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1013_ = v_json_1005_;
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_n_1011_);
lean_dec(v_json_1005_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_mantissa_1015_; lean_object* v_exponent_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1032_; 
v_mantissa_1015_ = lean_ctor_get(v_n_1011_, 0);
v_exponent_1016_ = lean_ctor_get(v_n_1011_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_n_1011_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1018_ = v_n_1011_;
v_isShared_1019_ = v_isSharedCheck_1032_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_exponent_1016_);
lean_inc(v_mantissa_1015_);
lean_dec(v_n_1011_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1032_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_natZero_1020_; lean_object* v_intZero_1021_; uint8_t v_isNeg_1022_; 
v_natZero_1020_ = lean_unsigned_to_nat(0u);
v_intZero_1021_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1022_ = lean_int_dec_lt(v_mantissa_1015_, v_intZero_1021_);
if (v_isNeg_1022_ == 0)
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_nat_dec_eq(v_exponent_1016_, v_natZero_1020_);
lean_dec(v_exponent_1016_);
if (v___x_1023_ == 0)
{
lean_del_object(v___x_1018_);
lean_dec(v_mantissa_1015_);
lean_del_object(v___x_1013_);
lean_dec_ref(v_a_1006_);
goto v___jp_1008_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v_a_1024_ = lean_nat_abs(v_mantissa_1015_);
lean_dec(v_mantissa_1015_);
v___x_1025_ = l_Lean_Expr_bvar___override(v_a_1024_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_a_1006_);
lean_ctor_set(v___x_1018_, 0, v___x_1025_);
v___x_1027_ = v___x_1018_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1006_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1027_);
v___x_1029_ = v___x_1013_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_del_object(v___x_1018_);
lean_dec(v_exponent_1016_);
lean_dec(v_mantissa_1015_);
lean_del_object(v___x_1013_);
lean_dec_ref(v_a_1006_);
goto v___jp_1008_;
}
}
}
}
else
{
lean_dec_ref(v_a_1006_);
lean_dec(v_json_1005_);
goto v___jp_1008_;
}
v___jp_1008_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___closed__1));
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar___boxed(lean_object* v_json_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_json_1034_, v_a_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(lean_object* v_json_1041_, lean_object* v_a_1042_){
_start:
{
if (lean_obj_tag(v_json_1041_) == 2)
{
lean_object* v_n_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1083_; 
v_n_1047_ = lean_ctor_get(v_json_1041_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_json_1041_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1049_ = v_json_1041_;
v_isShared_1050_ = v_isSharedCheck_1083_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_n_1047_);
lean_dec(v_json_1041_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1083_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_mantissa_1051_; lean_object* v_exponent_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1082_; 
v_mantissa_1051_ = lean_ctor_get(v_n_1047_, 0);
v_exponent_1052_ = lean_ctor_get(v_n_1047_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_n_1047_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1054_ = v_n_1047_;
v_isShared_1055_ = v_isSharedCheck_1082_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_exponent_1052_);
lean_inc(v_mantissa_1051_);
lean_dec(v_n_1047_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1082_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_natZero_1056_; lean_object* v_intZero_1057_; uint8_t v_isNeg_1058_; 
v_natZero_1056_ = lean_unsigned_to_nat(0u);
v_intZero_1057_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1058_ = lean_int_dec_lt(v_mantissa_1051_, v_intZero_1057_);
if (v_isNeg_1058_ == 0)
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_eq(v_exponent_1052_, v_natZero_1056_);
lean_dec(v_exponent_1052_);
if (v___x_1059_ == 0)
{
lean_del_object(v___x_1054_);
lean_dec(v_mantissa_1051_);
lean_del_object(v___x_1049_);
lean_dec_ref(v_a_1042_);
goto v___jp_1044_;
}
else
{
lean_object* v_levelMap_1060_; lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_levelMap_1060_ = lean_ctor_get(v_a_1042_, 2);
v_a_1061_ = lean_nat_abs(v_mantissa_1051_);
lean_dec(v_mantissa_1051_);
v___x_1062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1061_);
lean_del_object(v___x_1049_);
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_Expr_sort___override(v_val_1063_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_a_1042_);
lean_ctor_set(v___x_1054_, 0, v___x_1067_);
v___x_1069_ = v___x_1054_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1042_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v___x_1062_);
lean_del_object(v___x_1054_);
lean_dec_ref(v_a_1042_);
v___x_1075_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1076_ = l_Nat_reprFast(v_a_1061_);
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
lean_dec_ref(v___x_1076_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 18);
lean_ctor_set(v___x_1049_, 0, v___x_1077_);
v___x_1079_ = v___x_1049_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
}
else
{
lean_del_object(v___x_1054_);
lean_dec(v_exponent_1052_);
lean_dec(v_mantissa_1051_);
lean_del_object(v___x_1049_);
lean_dec_ref(v_a_1042_);
goto v___jp_1044_;
}
}
}
}
else
{
lean_dec_ref(v_a_1042_);
lean_dec(v_json_1041_);
goto v___jp_1044_;
}
v___jp_1044_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___closed__1));
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort___boxed(lean_object* v_json_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_json_1084_, v_a_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_bs_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_bs_1093_);
lean_ctor_set(v___x_1100_, 1, v___y_1094_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v_v_1102_; 
v_v_1102_ = lean_array_uget(v_bs_1093_, v_i_1092_);
if (lean_obj_tag(v_v_1102_) == 2)
{
lean_object* v_n_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1129_; 
v_n_1103_ = lean_ctor_get(v_v_1102_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_v_1102_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1105_ = v_v_1102_;
v_isShared_1106_ = v_isSharedCheck_1129_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_n_1103_);
lean_dec(v_v_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1129_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_mantissa_1107_; lean_object* v_exponent_1108_; lean_object* v_natZero_1109_; lean_object* v_intZero_1110_; uint8_t v_isNeg_1111_; 
v_mantissa_1107_ = lean_ctor_get(v_n_1103_, 0);
lean_inc(v_mantissa_1107_);
v_exponent_1108_ = lean_ctor_get(v_n_1103_, 1);
lean_inc(v_exponent_1108_);
lean_dec_ref(v_n_1103_);
v_natZero_1109_ = lean_unsigned_to_nat(0u);
v_intZero_1110_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1111_ = lean_int_dec_lt(v_mantissa_1107_, v_intZero_1110_);
if (v_isNeg_1111_ == 0)
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_nat_dec_eq(v_exponent_1108_, v_natZero_1109_);
lean_dec(v_exponent_1108_);
if (v___x_1112_ == 0)
{
lean_dec(v_mantissa_1107_);
lean_del_object(v___x_1105_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_bs_1093_);
goto v___jp_1096_;
}
else
{
lean_object* v_levelMap_1113_; lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_levelMap_1113_ = lean_ctor_get(v___y_1094_, 2);
v_a_1114_ = lean_nat_abs(v_mantissa_1107_);
lean_dec(v_mantissa_1107_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_levelMap_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1115_) == 1)
{
lean_object* v_val_1116_; lean_object* v_bs_x27_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_a_1114_);
lean_del_object(v___x_1105_);
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v_bs_x27_1117_ = lean_array_uset(v_bs_1093_, v_i_1092_, v_natZero_1109_);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1092_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1117_, v_i_1092_, v_val_1116_);
v_i_1092_ = v___x_1119_;
v_bs_1093_ = v___x_1120_;
goto _start;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec(v___x_1115_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_bs_1093_);
v___x_1122_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getLevel___closed__0));
v___x_1123_ = l_Nat_reprFast(v_a_1114_);
v___x_1124_ = lean_string_append(v___x_1122_, v___x_1123_);
lean_dec_ref(v___x_1123_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 18);
lean_ctor_set(v___x_1105_, 0, v___x_1124_);
v___x_1126_ = v___x_1105_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
else
{
lean_dec(v_exponent_1108_);
lean_dec(v_mantissa_1107_);
lean_del_object(v___x_1105_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_bs_1093_);
goto v___jp_1096_;
}
}
}
else
{
lean_dec(v_v_1102_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_bs_1093_);
goto v___jp_1096_;
}
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___boxed(lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_bs_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_boxed_1135_, v_i_boxed_1136_, v_bs_1132_, v___y_1133_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(lean_object* v_json_1140_, lean_object* v_a_1141_){
_start:
{
if (lean_obj_tag(v_json_1140_) == 5)
{
lean_object* v_kvPairs_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_kvPairs_1149_ = lean_ctor_get(v_json_1140_, 0);
v___x_1150_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1149_, v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 1)
{
lean_object* v_val_1152_; 
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1151_, 1);
if (lean_obj_tag(v_val_1152_) == 2)
{
lean_object* v_n_1153_; lean_object* v_mantissa_1154_; lean_object* v_exponent_1155_; lean_object* v_natZero_1156_; lean_object* v_intZero_1157_; uint8_t v_isNeg_1158_; 
v_n_1153_ = lean_ctor_get(v_val_1152_, 0);
lean_inc_ref(v_n_1153_);
lean_dec_ref_known(v_val_1152_, 1);
v_mantissa_1154_ = lean_ctor_get(v_n_1153_, 0);
lean_inc(v_mantissa_1154_);
v_exponent_1155_ = lean_ctor_get(v_n_1153_, 1);
lean_inc(v_exponent_1155_);
lean_dec_ref(v_n_1153_);
v_natZero_1156_ = lean_unsigned_to_nat(0u);
v_intZero_1157_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1158_ = lean_int_dec_lt(v_mantissa_1154_, v_intZero_1157_);
if (v_isNeg_1158_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_eq(v_exponent_1155_, v_natZero_1156_);
lean_dec(v_exponent_1155_);
if (v___x_1159_ == 0)
{
lean_dec(v_mantissa_1154_);
lean_dec_ref(v_a_1141_);
goto v___jp_1143_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__1));
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1149_, v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1214_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1214_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1214_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
if (lean_obj_tag(v_val_1162_) == 4)
{
lean_object* v_elems_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1213_; 
v_elems_1166_ = lean_ctor_get(v_val_1162_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_val_1162_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1168_ = v_val_1162_;
v_isShared_1169_ = v_isSharedCheck_1213_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_elems_1166_);
lean_dec(v_val_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1213_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_nameMap_1170_; lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_nameMap_1170_ = lean_ctor_get(v_a_1141_, 1);
v_a_1171_ = lean_nat_abs(v_mantissa_1154_);
lean_dec(v_mantissa_1154_);
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_a_1171_);
lean_del_object(v___x_1168_);
lean_del_object(v___x_1164_);
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v_sz_1174_ = lean_array_size(v_elems_1166_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0(v_sz_1174_, v___x_1175_, v_elems_1166_, v_a_1141_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1195_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1195_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1195_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1194_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1184_ = v_a_1177_;
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1181_);
lean_dec(v_a_1177_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = lean_array_to_list(v_fst_1181_);
v___x_1187_ = l_Lean_Expr_const___override(v_val_1173_, v___x_1186_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_snd_1182_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1189_);
v___x_1191_ = v___x_1179_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_val_1173_);
v_a_1196_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1176_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1176_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec(v___x_1172_);
lean_dec_ref(v_elems_1166_);
lean_dec_ref(v_a_1141_);
v___x_1204_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1205_ = l_Nat_reprFast(v_a_1171_);
v___x_1206_ = lean_string_append(v___x_1204_, v___x_1205_);
lean_dec_ref(v___x_1205_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 18);
lean_ctor_set(v___x_1168_, 0, v___x_1206_);
v___x_1208_ = v___x_1168_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1208_);
v___x_1210_ = v___x_1164_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
lean_del_object(v___x_1164_);
lean_dec(v_val_1162_);
lean_dec(v_mantissa_1154_);
lean_dec_ref(v_a_1141_);
goto v___jp_1146_;
}
}
}
else
{
lean_dec(v___x_1161_);
lean_dec(v_mantissa_1154_);
lean_dec_ref(v_a_1141_);
goto v___jp_1146_;
}
}
}
else
{
lean_dec(v_exponent_1155_);
lean_dec(v_mantissa_1154_);
lean_dec_ref(v_a_1141_);
goto v___jp_1143_;
}
}
else
{
lean_dec(v_val_1152_);
lean_dec_ref(v_a_1141_);
goto v___jp_1143_;
}
}
else
{
lean_dec(v___x_1151_);
lean_dec_ref(v_a_1141_);
goto v___jp_1143_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_a_1141_);
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
v___jp_1143_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
v___jp_1146_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst_spec__0___closed__1));
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___boxed(lean_object* v_json_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_json_1217_, v_a_1218_);
lean_dec(v_json_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(lean_object* v_json_1226_, lean_object* v_a_1227_){
_start:
{
if (lean_obj_tag(v_json_1226_) == 5)
{
lean_object* v_kvPairs_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_kvPairs_1235_ = lean_ctor_get(v_json_1226_, 0);
v___x_1236_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__2));
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1235_, v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1237_, 1);
if (lean_obj_tag(v_val_1238_) == 2)
{
lean_object* v_n_1239_; lean_object* v_mantissa_1240_; lean_object* v_exponent_1241_; lean_object* v_natZero_1242_; lean_object* v_intZero_1243_; uint8_t v_isNeg_1244_; 
v_n_1239_ = lean_ctor_get(v_val_1238_, 0);
lean_inc_ref(v_n_1239_);
lean_dec_ref_known(v_val_1238_, 1);
v_mantissa_1240_ = lean_ctor_get(v_n_1239_, 0);
lean_inc(v_mantissa_1240_);
v_exponent_1241_ = lean_ctor_get(v_n_1239_, 1);
lean_inc(v_exponent_1241_);
lean_dec_ref(v_n_1239_);
v_natZero_1242_ = lean_unsigned_to_nat(0u);
v_intZero_1243_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1244_ = lean_int_dec_lt(v_mantissa_1240_, v_intZero_1243_);
if (v_isNeg_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_nat_dec_eq(v_exponent_1241_, v_natZero_1242_);
lean_dec(v_exponent_1241_);
if (v___x_1245_ == 0)
{
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__3));
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1235_, v___x_1246_);
if (lean_obj_tag(v___x_1247_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1305_; 
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1305_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_val_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1305_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_val_1248_) == 2)
{
lean_object* v_n_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1304_; 
v_n_1252_ = lean_ctor_get(v_val_1248_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_val_1248_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1254_ = v_val_1248_;
v_isShared_1255_ = v_isSharedCheck_1304_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_n_1252_);
lean_dec(v_val_1248_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1304_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_mantissa_1256_; lean_object* v_exponent_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1303_; 
v_mantissa_1256_ = lean_ctor_get(v_n_1252_, 0);
v_exponent_1257_ = lean_ctor_get(v_n_1252_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_n_1252_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1259_ = v_n_1252_;
v_isShared_1260_ = v_isSharedCheck_1303_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_exponent_1257_);
lean_inc(v_mantissa_1256_);
lean_dec(v_n_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1303_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
uint8_t v_isNeg_1261_; 
v_isNeg_1261_ = lean_int_dec_lt(v_mantissa_1256_, v_intZero_1243_);
if (v_isNeg_1261_ == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_exponent_1257_, v_natZero_1242_);
lean_dec(v_exponent_1257_);
if (v___x_1262_ == 0)
{
lean_del_object(v___x_1259_);
lean_dec(v_mantissa_1256_);
lean_del_object(v___x_1254_);
lean_del_object(v___x_1250_);
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1232_;
}
else
{
lean_object* v_exprMap_1263_; lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_exprMap_1263_ = lean_ctor_get(v_a_1227_, 3);
v_a_1264_ = lean_nat_abs(v_mantissa_1240_);
lean_dec(v_mantissa_1240_);
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1265_) == 1)
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_a_1264_);
lean_del_object(v___x_1250_);
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1293_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1293_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_nat_abs(v_mantissa_1256_);
lean_dec(v_mantissa_1256_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1263_, v_a_1270_);
if (lean_obj_tag(v___x_1271_) == 1)
{
lean_object* v_val_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_a_1270_);
lean_del_object(v___x_1268_);
lean_del_object(v___x_1254_);
v_val_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_val_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = l_Lean_Expr_app___override(v_val_1266_, v_val_1272_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_a_1227_);
lean_ctor_set(v___x_1259_, 0, v___x_1276_);
v___x_1278_ = v___x_1259_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1227_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 0);
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
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v___x_1271_);
lean_dec(v_val_1266_);
lean_del_object(v___x_1259_);
lean_dec_ref(v_a_1227_);
v___x_1284_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1285_ = l_Nat_reprFast(v_a_1270_);
v___x_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
lean_dec_ref(v___x_1285_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 18);
lean_ctor_set(v___x_1268_, 0, v___x_1286_);
v___x_1288_ = v___x_1268_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1290_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 1);
lean_ctor_set(v___x_1254_, 0, v___x_1288_);
v___x_1290_ = v___x_1254_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_dec(v___x_1265_);
lean_del_object(v___x_1259_);
lean_dec(v_mantissa_1256_);
lean_dec_ref(v_a_1227_);
v___x_1294_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1295_ = l_Nat_reprFast(v_a_1264_);
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
lean_dec_ref(v___x_1295_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 18);
lean_ctor_set(v___x_1254_, 0, v___x_1296_);
v___x_1298_ = v___x_1254_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1298_);
v___x_1300_ = v___x_1250_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
else
{
lean_del_object(v___x_1259_);
lean_dec(v_exponent_1257_);
lean_dec(v_mantissa_1256_);
lean_del_object(v___x_1254_);
lean_del_object(v___x_1250_);
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1232_;
}
}
}
}
else
{
lean_del_object(v___x_1250_);
lean_dec(v_val_1248_);
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1232_;
}
}
}
else
{
lean_dec(v___x_1247_);
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1232_;
}
}
}
else
{
lean_dec(v_exponent_1241_);
lean_dec(v_mantissa_1240_);
lean_dec_ref(v_a_1227_);
goto v___jp_1229_;
}
}
else
{
lean_dec(v_val_1238_);
lean_dec_ref(v_a_1227_);
goto v___jp_1229_;
}
}
else
{
lean_dec(v___x_1237_);
lean_dec_ref(v_a_1227_);
goto v___jp_1229_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_a_1227_);
v___x_1306_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
v___jp_1229_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
v___jp_1232_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___closed__1));
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp___boxed(lean_object* v_json_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_json_1308_, v_a_1309_);
lean_dec(v_json_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(lean_object* v_info_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__0));
v___x_1321_ = lean_string_dec_eq(v_info_1317_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__1));
v___x_1323_ = lean_string_dec_eq(v_info_1317_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__2));
v___x_1325_ = lean_string_dec_eq(v_info_1317_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__3));
v___x_1327_ = lean_string_dec_eq(v_info_1317_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_a_1318_);
v___x_1328_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___closed__4));
v___x_1329_ = lean_string_append(v___x_1328_, v_info_1317_);
v___x_1330_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
else
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = 3;
v___x_1333_ = lean_box(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_a_1318_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
else
{
uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = 2;
v___x_1337_ = lean_box(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_a_1318_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
}
else
{
uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = 1;
v___x_1341_ = lean_box(v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_a_1318_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
else
{
uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1344_ = 0;
v___x_1345_ = lean_box(v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_a_1318_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo___boxed(lean_object* v_info_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_info_1348_, v_a_1349_);
lean_dec_ref(v_info_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(lean_object* v_json_1358_, lean_object* v_a_1359_){
_start:
{
if (lean_obj_tag(v_json_1358_) == 5)
{
lean_object* v_kvPairs_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_kvPairs_1373_ = lean_ctor_get(v_json_1358_, 0);
v___x_1374_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1373_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 1)
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1375_, 1);
if (lean_obj_tag(v_val_1376_) == 2)
{
lean_object* v_n_1377_; lean_object* v_mantissa_1378_; lean_object* v_exponent_1379_; lean_object* v_natZero_1380_; lean_object* v_intZero_1381_; uint8_t v_isNeg_1382_; 
v_n_1377_ = lean_ctor_get(v_val_1376_, 0);
lean_inc_ref(v_n_1377_);
lean_dec_ref_known(v_val_1376_, 1);
v_mantissa_1378_ = lean_ctor_get(v_n_1377_, 0);
lean_inc(v_mantissa_1378_);
v_exponent_1379_ = lean_ctor_get(v_n_1377_, 1);
lean_inc(v_exponent_1379_);
lean_dec_ref(v_n_1377_);
v_natZero_1380_ = lean_unsigned_to_nat(0u);
v_intZero_1381_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1382_ = lean_int_dec_lt(v_mantissa_1378_, v_intZero_1381_);
if (v_isNeg_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_eq(v_exponent_1379_, v_natZero_1380_);
lean_dec(v_exponent_1379_);
if (v___x_1383_ == 0)
{
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1361_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1373_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 1)
{
lean_object* v_val_1386_; 
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1385_, 1);
if (lean_obj_tag(v_val_1386_) == 2)
{
lean_object* v_n_1387_; lean_object* v_mantissa_1388_; lean_object* v_exponent_1389_; uint8_t v_isNeg_1390_; 
v_n_1387_ = lean_ctor_get(v_val_1386_, 0);
lean_inc_ref(v_n_1387_);
lean_dec_ref_known(v_val_1386_, 1);
v_mantissa_1388_ = lean_ctor_get(v_n_1387_, 0);
lean_inc(v_mantissa_1388_);
v_exponent_1389_ = lean_ctor_get(v_n_1387_, 1);
lean_inc(v_exponent_1389_);
lean_dec_ref(v_n_1387_);
v_isNeg_1390_ = lean_int_dec_lt(v_mantissa_1388_, v_intZero_1381_);
if (v_isNeg_1390_ == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_nat_dec_eq(v_exponent_1389_, v_natZero_1380_);
lean_dec(v_exponent_1389_);
if (v___x_1391_ == 0)
{
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1364_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1373_, v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 1)
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1393_, 1);
if (lean_obj_tag(v_val_1394_) == 2)
{
lean_object* v_n_1395_; lean_object* v_mantissa_1396_; lean_object* v_exponent_1397_; uint8_t v_isNeg_1398_; 
v_n_1395_ = lean_ctor_get(v_val_1394_, 0);
lean_inc_ref(v_n_1395_);
lean_dec_ref_known(v_val_1394_, 1);
v_mantissa_1396_ = lean_ctor_get(v_n_1395_, 0);
lean_inc(v_mantissa_1396_);
v_exponent_1397_ = lean_ctor_get(v_n_1395_, 1);
lean_inc(v_exponent_1397_);
lean_dec_ref(v_n_1395_);
v_isNeg_1398_ = lean_int_dec_lt(v_mantissa_1396_, v_intZero_1381_);
if (v_isNeg_1398_ == 0)
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_eq(v_exponent_1397_, v_natZero_1380_);
lean_dec(v_exponent_1397_);
if (v___x_1399_ == 0)
{
lean_dec(v_mantissa_1396_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1373_, v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1485_; 
v_val_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1485_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_val_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1485_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
if (lean_obj_tag(v_val_1402_) == 3)
{
lean_object* v_s_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1484_; 
v_s_1406_ = lean_ctor_get(v_val_1402_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_val_1402_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1408_ = v_val_1402_;
v_isShared_1409_ = v_isSharedCheck_1484_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_s_1406_);
lean_dec(v_val_1402_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1484_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_nameMap_1410_; lean_object* v_exprMap_1411_; lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_nameMap_1410_ = lean_ctor_get(v_a_1359_, 1);
v_exprMap_1411_ = lean_ctor_get(v_a_1359_, 3);
v_a_1412_ = lean_nat_abs(v_mantissa_1378_);
lean_dec(v_mantissa_1378_);
v___x_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1410_, v_a_1412_);
if (lean_obj_tag(v___x_1413_) == 1)
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1412_);
lean_del_object(v___x_1404_);
v_val_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1474_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1474_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_nat_abs(v_mantissa_1388_);
lean_dec(v_mantissa_1388_);
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1411_, v_a_1418_);
if (lean_obj_tag(v___x_1419_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_a_1418_);
lean_del_object(v___x_1408_);
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1464_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1464_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_nat_abs(v_mantissa_1396_);
lean_dec(v_mantissa_1396_);
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1411_, v_a_1424_);
if (lean_obj_tag(v___x_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; 
lean_dec(v_a_1424_);
lean_del_object(v___x_1422_);
lean_del_object(v___x_1416_);
v_val_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1406_, v_a_1359_);
lean_dec_ref(v_s_1406_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1446_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1445_; 
v_fst_1432_ = lean_ctor_get(v_a_1428_, 0);
v_snd_1433_ = lean_ctor_get(v_a_1428_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1435_ = v_a_1428_;
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1433_);
lean_inc(v_fst_1432_);
lean_dec(v_a_1428_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = lean_unbox(v_fst_1432_);
lean_dec(v_fst_1432_);
v___x_1438_ = l_Lean_Expr_lam___override(v_val_1414_, v_val_1420_, v_val_1426_, v___x_1437_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1433_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1440_);
v___x_1442_ = v___x_1430_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_val_1426_);
lean_dec(v_val_1420_);
lean_dec(v_val_1414_);
v_a_1447_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1427_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1427_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec(v___x_1425_);
lean_dec(v_val_1420_);
lean_dec(v_val_1414_);
lean_dec_ref(v_s_1406_);
lean_dec_ref(v_a_1359_);
v___x_1455_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1456_ = l_Nat_reprFast(v_a_1424_);
v___x_1457_ = lean_string_append(v___x_1455_, v___x_1456_);
lean_dec_ref(v___x_1456_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 18);
lean_ctor_set(v___x_1422_, 0, v___x_1457_);
v___x_1459_ = v___x_1422_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1459_);
v___x_1461_ = v___x_1416_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
lean_dec(v___x_1419_);
lean_dec(v_val_1414_);
lean_dec_ref(v_s_1406_);
lean_dec(v_mantissa_1396_);
lean_dec_ref(v_a_1359_);
v___x_1465_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1466_ = l_Nat_reprFast(v_a_1418_);
v___x_1467_ = lean_string_append(v___x_1465_, v___x_1466_);
lean_dec_ref(v___x_1466_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 18);
lean_ctor_set(v___x_1416_, 0, v___x_1467_);
v___x_1469_ = v___x_1416_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 1);
lean_ctor_set(v___x_1408_, 0, v___x_1469_);
v___x_1471_ = v___x_1408_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v___x_1413_);
lean_dec_ref(v_s_1406_);
lean_dec(v_mantissa_1396_);
lean_dec(v_mantissa_1388_);
lean_dec_ref(v_a_1359_);
v___x_1475_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1476_ = l_Nat_reprFast(v_a_1412_);
v___x_1477_ = lean_string_append(v___x_1475_, v___x_1476_);
lean_dec_ref(v___x_1476_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 18);
lean_ctor_set(v___x_1408_, 0, v___x_1477_);
v___x_1479_ = v___x_1408_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1479_);
v___x_1481_ = v___x_1404_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
else
{
lean_del_object(v___x_1404_);
lean_dec(v_val_1402_);
lean_dec(v_mantissa_1396_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1370_;
}
}
}
else
{
lean_dec(v___x_1401_);
lean_dec(v_mantissa_1396_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1370_;
}
}
}
else
{
lean_dec(v_exponent_1397_);
lean_dec(v_mantissa_1396_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1367_;
}
}
else
{
lean_dec(v_val_1394_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1367_;
}
}
else
{
lean_dec(v___x_1393_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1367_;
}
}
}
else
{
lean_dec(v_exponent_1389_);
lean_dec(v_mantissa_1388_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1364_;
}
}
else
{
lean_dec(v_val_1386_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1364_;
}
}
else
{
lean_dec(v___x_1385_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1364_;
}
}
}
else
{
lean_dec(v_exponent_1379_);
lean_dec(v_mantissa_1378_);
lean_dec_ref(v_a_1359_);
goto v___jp_1361_;
}
}
else
{
lean_dec(v_val_1376_);
lean_dec_ref(v_a_1359_);
goto v___jp_1361_;
}
}
else
{
lean_dec(v___x_1375_);
lean_dec_ref(v_a_1359_);
goto v___jp_1361_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_a_1359_);
v___x_1486_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
v___jp_1364_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
v___jp_1367_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
v___jp_1370_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__1));
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___boxed(lean_object* v_json_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_json_1488_, v_a_1489_);
lean_dec(v_json_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(lean_object* v_json_1495_, lean_object* v_a_1496_){
_start:
{
if (lean_obj_tag(v_json_1495_) == 5)
{
lean_object* v_kvPairs_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_kvPairs_1510_ = lean_ctor_get(v_json_1495_, 0);
v___x_1511_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1510_, v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 1)
{
lean_object* v_val_1513_; 
v_val_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v___x_1512_, 1);
if (lean_obj_tag(v_val_1513_) == 2)
{
lean_object* v_n_1514_; lean_object* v_mantissa_1515_; lean_object* v_exponent_1516_; lean_object* v_natZero_1517_; lean_object* v_intZero_1518_; uint8_t v_isNeg_1519_; 
v_n_1514_ = lean_ctor_get(v_val_1513_, 0);
lean_inc_ref(v_n_1514_);
lean_dec_ref_known(v_val_1513_, 1);
v_mantissa_1515_ = lean_ctor_get(v_n_1514_, 0);
lean_inc(v_mantissa_1515_);
v_exponent_1516_ = lean_ctor_get(v_n_1514_, 1);
lean_inc(v_exponent_1516_);
lean_dec_ref(v_n_1514_);
v_natZero_1517_ = lean_unsigned_to_nat(0u);
v_intZero_1518_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1519_ = lean_int_dec_lt(v_mantissa_1515_, v_intZero_1518_);
if (v_isNeg_1519_ == 0)
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_nat_dec_eq(v_exponent_1516_, v_natZero_1517_);
lean_dec(v_exponent_1516_);
if (v___x_1520_ == 0)
{
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1498_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1510_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
if (lean_obj_tag(v_val_1523_) == 2)
{
lean_object* v_n_1524_; lean_object* v_mantissa_1525_; lean_object* v_exponent_1526_; uint8_t v_isNeg_1527_; 
v_n_1524_ = lean_ctor_get(v_val_1523_, 0);
lean_inc_ref(v_n_1524_);
lean_dec_ref_known(v_val_1523_, 1);
v_mantissa_1525_ = lean_ctor_get(v_n_1524_, 0);
lean_inc(v_mantissa_1525_);
v_exponent_1526_ = lean_ctor_get(v_n_1524_, 1);
lean_inc(v_exponent_1526_);
lean_dec_ref(v_n_1524_);
v_isNeg_1527_ = lean_int_dec_lt(v_mantissa_1525_, v_intZero_1518_);
if (v_isNeg_1527_ == 0)
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_eq(v_exponent_1526_, v_natZero_1517_);
lean_dec(v_exponent_1526_);
if (v___x_1528_ == 0)
{
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1501_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1510_, v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 1)
{
lean_object* v_val_1531_; 
v_val_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1530_, 1);
if (lean_obj_tag(v_val_1531_) == 2)
{
lean_object* v_n_1532_; lean_object* v_mantissa_1533_; lean_object* v_exponent_1534_; uint8_t v_isNeg_1535_; 
v_n_1532_ = lean_ctor_get(v_val_1531_, 0);
lean_inc_ref(v_n_1532_);
lean_dec_ref_known(v_val_1531_, 1);
v_mantissa_1533_ = lean_ctor_get(v_n_1532_, 0);
lean_inc(v_mantissa_1533_);
v_exponent_1534_ = lean_ctor_get(v_n_1532_, 1);
lean_inc(v_exponent_1534_);
lean_dec_ref(v_n_1532_);
v_isNeg_1535_ = lean_int_dec_lt(v_mantissa_1533_, v_intZero_1518_);
if (v_isNeg_1535_ == 0)
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_nat_dec_eq(v_exponent_1534_, v_natZero_1517_);
lean_dec(v_exponent_1534_);
if (v___x_1536_ == 0)
{
lean_dec(v_mantissa_1533_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1504_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__4));
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1510_, v___x_1537_);
if (lean_obj_tag(v___x_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1622_; 
v_val_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1622_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_val_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1622_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
if (lean_obj_tag(v_val_1539_) == 3)
{
lean_object* v_s_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1621_; 
v_s_1543_ = lean_ctor_get(v_val_1539_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_val_1539_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1545_ = v_val_1539_;
v_isShared_1546_ = v_isSharedCheck_1621_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_s_1543_);
lean_dec(v_val_1539_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1621_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_nameMap_1547_; lean_object* v_exprMap_1548_; lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_nameMap_1547_ = lean_ctor_get(v_a_1496_, 1);
v_exprMap_1548_ = lean_ctor_get(v_a_1496_, 3);
v_a_1549_ = lean_nat_abs(v_mantissa_1515_);
lean_dec(v_mantissa_1515_);
v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1547_, v_a_1549_);
if (lean_obj_tag(v___x_1550_) == 1)
{
lean_object* v_val_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1549_);
lean_del_object(v___x_1541_);
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1611_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_val_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1611_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_nat_abs(v_mantissa_1525_);
lean_dec(v_mantissa_1525_);
v___x_1556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1548_, v_a_1555_);
if (lean_obj_tag(v___x_1556_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1555_);
lean_del_object(v___x_1545_);
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1601_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1601_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_nat_abs(v_mantissa_1533_);
lean_dec(v_mantissa_1533_);
v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1548_, v_a_1561_);
if (lean_obj_tag(v___x_1562_) == 1)
{
lean_object* v_val_1563_; lean_object* v___x_1564_; 
lean_dec(v_a_1561_);
lean_del_object(v___x_1559_);
lean_del_object(v___x_1553_);
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseBinderInfo(v_s_1543_, v_a_1496_);
lean_dec_ref(v_s_1543_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1583_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1583_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1583_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1582_; 
v_fst_1569_ = lean_ctor_get(v_a_1565_, 0);
v_snd_1570_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1572_ = v_a_1565_;
v_isShared_1573_ = v_isSharedCheck_1582_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_inc(v_fst_1569_);
lean_dec(v_a_1565_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1582_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = lean_unbox(v_fst_1569_);
lean_dec(v_fst_1569_);
v___x_1575_ = l_Lean_Expr_forallE___override(v_val_1551_, v_val_1557_, v_val_1563_, v___x_1574_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1570_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1577_);
v___x_1579_ = v___x_1567_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_val_1563_);
lean_dec(v_val_1557_);
lean_dec(v_val_1551_);
v_a_1584_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1564_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1564_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v___x_1562_);
lean_dec(v_val_1557_);
lean_dec(v_val_1551_);
lean_dec_ref(v_s_1543_);
lean_dec_ref(v_a_1496_);
v___x_1592_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1593_ = l_Nat_reprFast(v_a_1561_);
v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
lean_dec_ref(v___x_1593_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 18);
lean_ctor_set(v___x_1559_, 0, v___x_1594_);
v___x_1596_ = v___x_1559_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1596_);
v___x_1598_ = v___x_1553_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_dec(v___x_1556_);
lean_dec(v_val_1551_);
lean_dec_ref(v_s_1543_);
lean_dec(v_mantissa_1533_);
lean_dec_ref(v_a_1496_);
v___x_1602_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1603_ = l_Nat_reprFast(v_a_1555_);
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
lean_dec_ref(v___x_1603_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 18);
lean_ctor_set(v___x_1553_, 0, v___x_1604_);
v___x_1606_ = v___x_1553_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 0, v___x_1606_);
v___x_1608_ = v___x_1545_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_dec(v___x_1550_);
lean_dec_ref(v_s_1543_);
lean_dec(v_mantissa_1533_);
lean_dec(v_mantissa_1525_);
lean_dec_ref(v_a_1496_);
v___x_1612_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1613_ = l_Nat_reprFast(v_a_1549_);
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
lean_dec_ref(v___x_1613_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 18);
lean_ctor_set(v___x_1545_, 0, v___x_1614_);
v___x_1616_ = v___x_1545_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1616_);
v___x_1618_ = v___x_1541_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
else
{
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
lean_dec(v_mantissa_1533_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1507_;
}
}
}
else
{
lean_dec(v___x_1538_);
lean_dec(v_mantissa_1533_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1507_;
}
}
}
else
{
lean_dec(v_exponent_1534_);
lean_dec(v_mantissa_1533_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1504_;
}
}
else
{
lean_dec(v_val_1531_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1504_;
}
}
else
{
lean_dec(v___x_1530_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1504_;
}
}
}
else
{
lean_dec(v_exponent_1526_);
lean_dec(v_mantissa_1525_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1501_;
}
}
else
{
lean_dec(v_val_1523_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1501_;
}
}
else
{
lean_dec(v___x_1522_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1501_;
}
}
}
else
{
lean_dec(v_exponent_1516_);
lean_dec(v_mantissa_1515_);
lean_dec_ref(v_a_1496_);
goto v___jp_1498_;
}
}
else
{
lean_dec(v_val_1513_);
lean_dec_ref(v_a_1496_);
goto v___jp_1498_;
}
}
else
{
lean_dec(v___x_1512_);
lean_dec_ref(v_a_1496_);
goto v___jp_1498_;
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_a_1496_);
v___x_1623_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
v___jp_1498_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
v___jp_1501_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
v___jp_1504_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
v___jp_1507_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___closed__1));
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE___boxed(lean_object* v_json_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_json_1625_, v_a_1626_);
lean_dec(v_json_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(lean_object* v_json_1634_, lean_object* v_a_1635_){
_start:
{
if (lean_obj_tag(v_json_1634_) == 5)
{
lean_object* v_kvPairs_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_kvPairs_1652_ = lean_ctor_get(v_json_1634_, 0);
v___x_1653_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_1654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1652_, v___x_1653_);
if (lean_obj_tag(v___x_1654_) == 1)
{
lean_object* v_val_1655_; 
v_val_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1654_, 1);
if (lean_obj_tag(v_val_1655_) == 2)
{
lean_object* v_n_1656_; lean_object* v_mantissa_1657_; lean_object* v_exponent_1658_; lean_object* v_natZero_1659_; lean_object* v_intZero_1660_; uint8_t v_isNeg_1661_; 
v_n_1656_ = lean_ctor_get(v_val_1655_, 0);
lean_inc_ref(v_n_1656_);
lean_dec_ref_known(v_val_1655_, 1);
v_mantissa_1657_ = lean_ctor_get(v_n_1656_, 0);
lean_inc(v_mantissa_1657_);
v_exponent_1658_ = lean_ctor_get(v_n_1656_, 1);
lean_inc(v_exponent_1658_);
lean_dec_ref(v_n_1656_);
v_natZero_1659_ = lean_unsigned_to_nat(0u);
v_intZero_1660_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1661_ = lean_int_dec_lt(v_mantissa_1657_, v_intZero_1660_);
if (v_isNeg_1661_ == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_eq(v_exponent_1658_, v_natZero_1659_);
lean_dec(v_exponent_1658_);
if (v___x_1662_ == 0)
{
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1637_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_1664_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1652_, v___x_1663_);
if (lean_obj_tag(v___x_1664_) == 1)
{
lean_object* v_val_1665_; 
v_val_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1664_, 1);
if (lean_obj_tag(v_val_1665_) == 2)
{
lean_object* v_n_1666_; lean_object* v_mantissa_1667_; lean_object* v_exponent_1668_; uint8_t v_isNeg_1669_; 
v_n_1666_ = lean_ctor_get(v_val_1665_, 0);
lean_inc_ref(v_n_1666_);
lean_dec_ref_known(v_val_1665_, 1);
v_mantissa_1667_ = lean_ctor_get(v_n_1666_, 0);
lean_inc(v_mantissa_1667_);
v_exponent_1668_ = lean_ctor_get(v_n_1666_, 1);
lean_inc(v_exponent_1668_);
lean_dec_ref(v_n_1666_);
v_isNeg_1669_ = lean_int_dec_lt(v_mantissa_1667_, v_intZero_1660_);
if (v_isNeg_1669_ == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_nat_dec_eq(v_exponent_1668_, v_natZero_1659_);
lean_dec(v_exponent_1668_);
if (v___x_1670_ == 0)
{
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1640_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_1672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1652_, v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 1)
{
lean_object* v_val_1673_; 
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v___x_1672_, 1);
if (lean_obj_tag(v_val_1673_) == 2)
{
lean_object* v_n_1674_; lean_object* v_mantissa_1675_; lean_object* v_exponent_1676_; uint8_t v_isNeg_1677_; 
v_n_1674_ = lean_ctor_get(v_val_1673_, 0);
lean_inc_ref(v_n_1674_);
lean_dec_ref_known(v_val_1673_, 1);
v_mantissa_1675_ = lean_ctor_get(v_n_1674_, 0);
lean_inc(v_mantissa_1675_);
v_exponent_1676_ = lean_ctor_get(v_n_1674_, 1);
lean_inc(v_exponent_1676_);
lean_dec_ref(v_n_1674_);
v_isNeg_1677_ = lean_int_dec_lt(v_mantissa_1675_, v_intZero_1660_);
if (v_isNeg_1677_ == 0)
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_nat_dec_eq(v_exponent_1676_, v_natZero_1659_);
lean_dec(v_exponent_1676_);
if (v___x_1678_ == 0)
{
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1643_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__3));
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1652_, v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 1)
{
lean_object* v_val_1681_; 
v_val_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v___x_1680_, 1);
if (lean_obj_tag(v_val_1681_) == 2)
{
lean_object* v_n_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1775_; 
v_n_1682_ = lean_ctor_get(v_val_1681_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_val_1681_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1684_ = v_val_1681_;
v_isShared_1685_ = v_isSharedCheck_1775_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_n_1682_);
lean_dec(v_val_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1775_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_mantissa_1686_; lean_object* v_exponent_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1774_; 
v_mantissa_1686_ = lean_ctor_get(v_n_1682_, 0);
v_exponent_1687_ = lean_ctor_get(v_n_1682_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_n_1682_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1689_ = v_n_1682_;
v_isShared_1690_ = v_isSharedCheck_1774_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_exponent_1687_);
lean_inc(v_mantissa_1686_);
lean_dec(v_n_1682_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1774_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
uint8_t v_isNeg_1691_; 
v_isNeg_1691_ = lean_int_dec_lt(v_mantissa_1686_, v_intZero_1660_);
if (v_isNeg_1691_ == 0)
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_nat_dec_eq(v_exponent_1687_, v_natZero_1659_);
lean_dec(v_exponent_1687_);
if (v___x_1692_ == 0)
{
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_del_object(v___x_1684_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1646_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__3));
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1652_, v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 1)
{
lean_object* v_val_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1773_; 
v_val_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1773_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_val_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1773_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
if (lean_obj_tag(v_val_1695_) == 1)
{
uint8_t v_b_1699_; lean_object* v_nameMap_1700_; lean_object* v_exprMap_1701_; lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_b_1699_ = lean_ctor_get_uint8(v_val_1695_, 0);
lean_dec_ref_known(v_val_1695_, 0);
v_nameMap_1700_ = lean_ctor_get(v_a_1635_, 1);
v_exprMap_1701_ = lean_ctor_get(v_a_1635_, 3);
v_a_1702_ = lean_nat_abs(v_mantissa_1657_);
lean_dec(v_mantissa_1657_);
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1700_, v_a_1702_);
if (lean_obj_tag(v___x_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1702_);
lean_del_object(v___x_1684_);
v_val_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1763_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1763_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_nat_abs(v_mantissa_1667_);
lean_dec(v_mantissa_1667_);
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1701_, v_a_1708_);
if (lean_obj_tag(v___x_1709_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1708_);
lean_del_object(v___x_1697_);
v_val_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1753_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_val_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1753_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1714_ = lean_nat_abs(v_mantissa_1675_);
lean_dec(v_mantissa_1675_);
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1701_, v_a_1714_);
if (lean_obj_tag(v___x_1715_) == 1)
{
lean_object* v_val_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1714_);
lean_del_object(v___x_1706_);
v_val_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1743_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_val_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1743_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_nat_abs(v_mantissa_1686_);
lean_dec(v_mantissa_1686_);
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1701_, v_a_1720_);
if (lean_obj_tag(v___x_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1720_);
lean_del_object(v___x_1718_);
lean_del_object(v___x_1712_);
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_val_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_Expr_letE___override(v_val_1704_, v_val_1710_, v_val_1716_, v_val_1722_, v_b_1699_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v_a_1635_);
lean_ctor_set(v___x_1689_, 0, v___x_1726_);
v___x_1728_ = v___x_1689_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1635_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1730_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1728_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec(v___x_1721_);
lean_dec(v_val_1716_);
lean_dec(v_val_1710_);
lean_dec(v_val_1704_);
lean_del_object(v___x_1689_);
lean_dec_ref(v_a_1635_);
v___x_1734_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1735_ = l_Nat_reprFast(v_a_1720_);
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
lean_dec_ref(v___x_1735_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set_tag(v___x_1718_, 18);
lean_ctor_set(v___x_1718_, 0, v___x_1736_);
v___x_1738_ = v___x_1718_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1738_);
v___x_1740_ = v___x_1712_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
lean_dec(v___x_1715_);
lean_dec(v_val_1710_);
lean_dec(v_val_1704_);
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_dec_ref(v_a_1635_);
v___x_1744_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1745_ = l_Nat_reprFast(v_a_1714_);
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
lean_dec_ref(v___x_1745_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 18);
lean_ctor_set(v___x_1712_, 0, v___x_1746_);
v___x_1748_ = v___x_1712_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1748_);
v___x_1750_ = v___x_1706_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v___x_1709_);
lean_dec(v_val_1704_);
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_dec(v_mantissa_1675_);
lean_dec_ref(v_a_1635_);
v___x_1754_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1755_ = l_Nat_reprFast(v_a_1708_);
v___x_1756_ = lean_string_append(v___x_1754_, v___x_1755_);
lean_dec_ref(v___x_1755_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 18);
lean_ctor_set(v___x_1706_, 0, v___x_1756_);
v___x_1758_ = v___x_1706_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1758_);
v___x_1760_ = v___x_1697_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v___x_1703_);
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec_ref(v_a_1635_);
v___x_1764_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1765_ = l_Nat_reprFast(v_a_1702_);
v___x_1766_ = lean_string_append(v___x_1764_, v___x_1765_);
lean_dec_ref(v___x_1765_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 18);
lean_ctor_set(v___x_1697_, 0, v___x_1766_);
v___x_1768_ = v___x_1697_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 1);
lean_ctor_set(v___x_1684_, 0, v___x_1768_);
v___x_1770_ = v___x_1684_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_del_object(v___x_1697_);
lean_dec(v_val_1695_);
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_del_object(v___x_1684_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1649_;
}
}
}
else
{
lean_dec(v___x_1694_);
lean_del_object(v___x_1689_);
lean_dec(v_mantissa_1686_);
lean_del_object(v___x_1684_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1649_;
}
}
}
else
{
lean_del_object(v___x_1689_);
lean_dec(v_exponent_1687_);
lean_dec(v_mantissa_1686_);
lean_del_object(v___x_1684_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1646_;
}
}
}
}
else
{
lean_dec(v_val_1681_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1646_;
}
}
else
{
lean_dec(v___x_1680_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1646_;
}
}
}
else
{
lean_dec(v_exponent_1676_);
lean_dec(v_mantissa_1675_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1643_;
}
}
else
{
lean_dec(v_val_1673_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1643_;
}
}
else
{
lean_dec(v___x_1672_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1643_;
}
}
}
else
{
lean_dec(v_exponent_1668_);
lean_dec(v_mantissa_1667_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1640_;
}
}
else
{
lean_dec(v_val_1665_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1640_;
}
}
else
{
lean_dec(v___x_1664_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1640_;
}
}
}
else
{
lean_dec(v_exponent_1658_);
lean_dec(v_mantissa_1657_);
lean_dec_ref(v_a_1635_);
goto v___jp_1637_;
}
}
else
{
lean_dec(v_val_1655_);
lean_dec_ref(v_a_1635_);
goto v___jp_1637_;
}
}
else
{
lean_dec(v___x_1654_);
lean_dec_ref(v_a_1635_);
goto v___jp_1637_;
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref(v_a_1635_);
v___x_1776_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
v___jp_1637_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
v___jp_1643_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
v___jp_1646_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
v___jp_1649_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__1));
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___boxed(lean_object* v_json_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_json_1778_, v_a_1779_);
lean_dec(v_json_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(lean_object* v_json_1788_, lean_object* v_a_1789_){
_start:
{
if (lean_obj_tag(v_json_1788_) == 5)
{
lean_object* v_kvPairs_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_kvPairs_1800_ = lean_ctor_get(v_json_1788_, 0);
v___x_1801_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__2));
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1800_, v___x_1801_);
if (lean_obj_tag(v___x_1802_) == 1)
{
lean_object* v_val_1803_; 
v_val_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1803_);
lean_dec_ref_known(v___x_1802_, 1);
if (lean_obj_tag(v_val_1803_) == 2)
{
lean_object* v_n_1804_; lean_object* v_mantissa_1805_; lean_object* v_exponent_1806_; lean_object* v_natZero_1807_; lean_object* v_intZero_1808_; uint8_t v_isNeg_1809_; 
v_n_1804_ = lean_ctor_get(v_val_1803_, 0);
lean_inc_ref(v_n_1804_);
lean_dec_ref_known(v_val_1803_, 1);
v_mantissa_1805_ = lean_ctor_get(v_n_1804_, 0);
lean_inc(v_mantissa_1805_);
v_exponent_1806_ = lean_ctor_get(v_n_1804_, 1);
lean_inc(v_exponent_1806_);
lean_dec_ref(v_n_1804_);
v_natZero_1807_ = lean_unsigned_to_nat(0u);
v_intZero_1808_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1809_ = lean_int_dec_lt(v_mantissa_1805_, v_intZero_1808_);
if (v_isNeg_1809_ == 0)
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_nat_dec_eq(v_exponent_1806_, v_natZero_1807_);
lean_dec(v_exponent_1806_);
if (v___x_1810_ == 0)
{
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1791_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__3));
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1800_, v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 1)
{
lean_object* v_val_1813_; 
v_val_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1813_);
lean_dec_ref_known(v___x_1812_, 1);
if (lean_obj_tag(v_val_1813_) == 2)
{
lean_object* v_n_1814_; lean_object* v_mantissa_1815_; lean_object* v_exponent_1816_; uint8_t v_isNeg_1817_; 
v_n_1814_ = lean_ctor_get(v_val_1813_, 0);
lean_inc_ref(v_n_1814_);
lean_dec_ref_known(v_val_1813_, 1);
v_mantissa_1815_ = lean_ctor_get(v_n_1814_, 0);
lean_inc(v_mantissa_1815_);
v_exponent_1816_ = lean_ctor_get(v_n_1814_, 1);
lean_inc(v_exponent_1816_);
lean_dec_ref(v_n_1814_);
v_isNeg_1817_ = lean_int_dec_lt(v_mantissa_1815_, v_intZero_1808_);
if (v_isNeg_1817_ == 0)
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_nat_dec_eq(v_exponent_1816_, v_natZero_1807_);
lean_dec(v_exponent_1816_);
if (v___x_1818_ == 0)
{
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__4));
v___x_1820_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1800_, v___x_1819_);
if (lean_obj_tag(v___x_1820_) == 1)
{
lean_object* v_val_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1880_; 
v_val_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1880_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_val_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1880_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
if (lean_obj_tag(v_val_1821_) == 2)
{
lean_object* v_n_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1879_; 
v_n_1825_ = lean_ctor_get(v_val_1821_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_val_1821_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1827_ = v_val_1821_;
v_isShared_1828_ = v_isSharedCheck_1879_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_n_1825_);
lean_dec(v_val_1821_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1879_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_mantissa_1829_; lean_object* v_exponent_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1878_; 
v_mantissa_1829_ = lean_ctor_get(v_n_1825_, 0);
v_exponent_1830_ = lean_ctor_get(v_n_1825_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_n_1825_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1832_ = v_n_1825_;
v_isShared_1833_ = v_isSharedCheck_1878_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_exponent_1830_);
lean_inc(v_mantissa_1829_);
lean_dec(v_n_1825_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1878_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v_isNeg_1834_; 
v_isNeg_1834_ = lean_int_dec_lt(v_mantissa_1829_, v_intZero_1808_);
if (v_isNeg_1834_ == 0)
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_nat_dec_eq(v_exponent_1830_, v_natZero_1807_);
lean_dec(v_exponent_1830_);
if (v___x_1835_ == 0)
{
lean_del_object(v___x_1832_);
lean_dec(v_mantissa_1829_);
lean_del_object(v___x_1827_);
lean_del_object(v___x_1823_);
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1797_;
}
else
{
lean_object* v_nameMap_1836_; lean_object* v_exprMap_1837_; lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_nameMap_1836_ = lean_ctor_get(v_a_1789_, 1);
v_exprMap_1837_ = lean_ctor_get(v_a_1789_, 3);
v_a_1838_ = lean_nat_abs(v_mantissa_1805_);
lean_dec(v_mantissa_1805_);
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_1836_, v_a_1838_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v_val_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1838_);
lean_del_object(v___x_1823_);
v_val_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1868_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_val_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1868_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_nat_abs(v_mantissa_1829_);
lean_dec(v_mantissa_1829_);
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1837_, v_a_1844_);
if (lean_obj_tag(v___x_1845_) == 1)
{
lean_object* v_val_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1844_);
lean_del_object(v___x_1842_);
lean_del_object(v___x_1827_);
v_val_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_val_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v_a_1850_ = lean_nat_abs(v_mantissa_1815_);
lean_dec(v_mantissa_1815_);
v___x_1851_ = l_Lean_Expr_proj___override(v_val_1840_, v_a_1850_, v_val_1846_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_a_1789_);
lean_ctor_set(v___x_1832_, 0, v___x_1851_);
v___x_1853_ = v___x_1832_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1789_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1853_);
v___x_1855_ = v___x_1848_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v___x_1845_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1832_);
lean_dec(v_mantissa_1815_);
lean_dec_ref(v_a_1789_);
v___x_1859_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_1860_ = l_Nat_reprFast(v_a_1844_);
v___x_1861_ = lean_string_append(v___x_1859_, v___x_1860_);
lean_dec_ref(v___x_1860_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 18);
lean_ctor_set(v___x_1842_, 0, v___x_1861_);
v___x_1863_ = v___x_1842_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1863_);
v___x_1865_ = v___x_1827_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
lean_dec(v___x_1839_);
lean_del_object(v___x_1832_);
lean_dec(v_mantissa_1829_);
lean_dec(v_mantissa_1815_);
lean_dec_ref(v_a_1789_);
v___x_1869_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_1870_ = l_Nat_reprFast(v_a_1838_);
v___x_1871_ = lean_string_append(v___x_1869_, v___x_1870_);
lean_dec_ref(v___x_1870_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 18);
lean_ctor_set(v___x_1827_, 0, v___x_1871_);
v___x_1873_ = v___x_1827_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1873_);
v___x_1875_ = v___x_1823_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_del_object(v___x_1832_);
lean_dec(v_exponent_1830_);
lean_dec(v_mantissa_1829_);
lean_del_object(v___x_1827_);
lean_del_object(v___x_1823_);
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1797_;
}
}
}
}
else
{
lean_del_object(v___x_1823_);
lean_dec(v_val_1821_);
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1797_;
}
}
}
else
{
lean_dec(v___x_1820_);
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1797_;
}
}
}
else
{
lean_dec(v_exponent_1816_);
lean_dec(v_mantissa_1815_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1794_;
}
}
else
{
lean_dec(v_val_1813_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1794_;
}
}
else
{
lean_dec(v___x_1812_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1794_;
}
}
}
else
{
lean_dec(v_exponent_1806_);
lean_dec(v_mantissa_1805_);
lean_dec_ref(v_a_1789_);
goto v___jp_1791_;
}
}
else
{
lean_dec(v_val_1803_);
lean_dec_ref(v_a_1789_);
goto v___jp_1791_;
}
}
else
{
lean_dec(v___x_1802_);
lean_dec_ref(v_a_1789_);
goto v___jp_1791_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v_a_1789_);
v___x_1881_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
v___jp_1797_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___closed__1));
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj___boxed(lean_object* v_json_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_json_1883_, v_a_1884_);
lean_dec(v_json_1883_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(lean_object* v_json_1890_, lean_object* v_a_1891_){
_start:
{
if (lean_obj_tag(v_json_1890_) == 3)
{
lean_object* v_s_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1918_; 
v_s_1893_ = lean_ctor_get(v_json_1890_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_json_1890_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1895_ = v_json_1890_;
v_isShared_1896_ = v_isSharedCheck_1918_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_s_1893_);
lean_dec(v_json_1890_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1918_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_string_utf8_byte_size(v_s_1893_);
v___x_1899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1899_, 0, v_s_1893_);
lean_ctor_set(v___x_1899_, 1, v___x_1897_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
v___x_1900_ = l_String_Slice_toNat_x3f(v___x_1899_);
lean_dec_ref_known(v___x_1899_, 3);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1913_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1913_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1913_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 0);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_val_1901_);
v___x_1906_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1907_ = l_Lean_Expr_lit___override(v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v_a_1891_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1908_);
v___x_1910_ = v___x_1895_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v___x_1900_);
lean_dec_ref(v_a_1891_);
v___x_1914_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 0, v___x_1914_);
v___x_1916_ = v___x_1895_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_a_1891_);
lean_dec(v_json_1890_);
v___x_1919_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___closed__1));
v___x_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit___boxed(lean_object* v_json_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_json_1921_, v_a_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(lean_object* v_json_1928_, lean_object* v_a_1929_){
_start:
{
if (lean_obj_tag(v_json_1928_) == 3)
{
lean_object* v_s_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_s_1931_ = lean_ctor_get(v_json_1928_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_json_1928_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1933_ = v_json_1928_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_s_1931_);
lean_dec(v_json_1928_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_s_1931_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = l_Lean_Expr_lit___override(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v_a_1929_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec_ref(v_a_1929_);
lean_dec(v_json_1928_);
v___x_1942_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___closed__1));
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit___boxed(lean_object* v_json_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_json_1944_, v_a_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(lean_object* v_json_1953_, lean_object* v_a_1954_){
_start:
{
if (lean_obj_tag(v_json_1953_) == 5)
{
lean_object* v_kvPairs_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_kvPairs_1962_ = lean_ctor_get(v_json_1953_, 0);
v___x_1963_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__2));
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1962_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 1)
{
lean_object* v_val_1965_; 
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_val_1965_) == 2)
{
lean_object* v_n_1966_; lean_object* v_mantissa_1967_; lean_object* v_exponent_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2013_; 
v_n_1966_ = lean_ctor_get(v_val_1965_, 0);
lean_inc_ref(v_n_1966_);
lean_dec_ref_known(v_val_1965_, 1);
v_mantissa_1967_ = lean_ctor_get(v_n_1966_, 0);
v_exponent_1968_ = lean_ctor_get(v_n_1966_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_n_1966_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1970_ = v_n_1966_;
v_isShared_1971_ = v_isSharedCheck_2013_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_exponent_1968_);
lean_inc(v_mantissa_1967_);
lean_dec(v_n_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2013_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_natZero_1972_; lean_object* v_intZero_1973_; uint8_t v_isNeg_1974_; 
v_natZero_1972_ = lean_unsigned_to_nat(0u);
v_intZero_1973_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_1974_ = lean_int_dec_lt(v_mantissa_1967_, v_intZero_1973_);
if (v_isNeg_1974_ == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_nat_dec_eq(v_exponent_1968_, v_natZero_1972_);
lean_dec(v_exponent_1968_);
if (v___x_1975_ == 0)
{
lean_del_object(v___x_1970_);
lean_dec(v_mantissa_1967_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__3));
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_1962_, v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2012_; 
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2012_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_val_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2012_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
if (lean_obj_tag(v_val_1978_) == 5)
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2010_; 
v_isSharedCheck_2010_ = !lean_is_exclusive(v_val_1978_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_val_1978_, 0);
lean_dec(v_unused_2011_);
v___x_1983_ = v_val_1978_;
v_isShared_1984_ = v_isSharedCheck_2010_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_val_1978_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2010_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_exprMap_1985_; lean_object* v_a_1986_; lean_object* v___x_1987_; 
v_exprMap_1985_ = lean_ctor_get(v_a_1954_, 3);
v_a_1986_ = lean_nat_abs(v_mantissa_1967_);
lean_dec(v_mantissa_1967_);
v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_a_1986_);
lean_del_object(v___x_1983_);
lean_del_object(v___x_1980_);
v_val_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = lean_box(0);
v___x_1993_ = l_Lean_Expr_mdata___override(v___x_1992_, v_val_1988_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v_a_1954_);
lean_ctor_set(v___x_1970_, 0, v___x_1993_);
v___x_1995_ = v___x_1970_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1954_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1995_);
v___x_1997_ = v___x_1990_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_dec(v___x_1987_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_a_1954_);
v___x_2001_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2002_ = l_Nat_reprFast(v_a_1986_);
v___x_2003_ = lean_string_append(v___x_2001_, v___x_2002_);
lean_dec_ref(v___x_2002_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 18);
lean_ctor_set(v___x_1983_, 0, v___x_2003_);
v___x_2005_ = v___x_1983_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2005_);
v___x_2007_ = v___x_1980_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
lean_del_object(v___x_1970_);
lean_dec(v_mantissa_1967_);
lean_dec_ref(v_a_1954_);
goto v___jp_1959_;
}
}
}
else
{
lean_dec(v___x_1977_);
lean_del_object(v___x_1970_);
lean_dec(v_mantissa_1967_);
lean_dec_ref(v_a_1954_);
goto v___jp_1959_;
}
}
}
else
{
lean_del_object(v___x_1970_);
lean_dec(v_exponent_1968_);
lean_dec(v_mantissa_1967_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
}
}
else
{
lean_dec(v_val_1965_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
}
else
{
lean_dec(v___x_1964_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v_a_1954_);
v___x_2014_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
v___jp_1956_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
v___jp_1959_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___closed__1));
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata___boxed(lean_object* v_json_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_json_2016_, v_a_2017_);
lean_dec(v_json_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = l_List_reverse___redArg(v_x_2024_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set(v___x_2031_, 1, v___y_2025_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v_head_2033_; 
v_head_2033_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_head_2033_);
if (lean_obj_tag(v_head_2033_) == 2)
{
lean_object* v_n_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2065_; 
v_n_2034_ = lean_ctor_get(v_head_2033_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_head_2033_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2036_ = v_head_2033_;
v_isShared_2037_ = v_isSharedCheck_2065_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_n_2034_);
lean_dec(v_head_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2065_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_tail_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2063_; 
v_tail_2038_ = lean_ctor_get(v_x_2023_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_x_2023_, 0);
lean_dec(v_unused_2064_);
v___x_2040_ = v_x_2023_;
v_isShared_2041_ = v_isSharedCheck_2063_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_tail_2038_);
lean_dec(v_x_2023_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2063_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_mantissa_2042_; lean_object* v_exponent_2043_; lean_object* v_natZero_2044_; lean_object* v_intZero_2045_; uint8_t v_isNeg_2046_; 
v_mantissa_2042_ = lean_ctor_get(v_n_2034_, 0);
lean_inc(v_mantissa_2042_);
v_exponent_2043_ = lean_ctor_get(v_n_2034_, 1);
lean_inc(v_exponent_2043_);
lean_dec_ref(v_n_2034_);
v_natZero_2044_ = lean_unsigned_to_nat(0u);
v_intZero_2045_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2046_ = lean_int_dec_lt(v_mantissa_2042_, v_intZero_2045_);
if (v_isNeg_2046_ == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_eq(v_exponent_2043_, v_natZero_2044_);
lean_dec(v_exponent_2043_);
if (v___x_2047_ == 0)
{
lean_dec(v_mantissa_2042_);
lean_del_object(v___x_2040_);
lean_dec(v_tail_2038_);
lean_del_object(v___x_2036_);
lean_dec_ref(v___y_2025_);
lean_dec(v_x_2024_);
goto v___jp_2027_;
}
else
{
lean_object* v_nameMap_2048_; lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_nameMap_2048_ = lean_ctor_get(v___y_2025_, 1);
v_a_2049_ = lean_nat_abs(v_mantissa_2042_);
lean_dec(v_mantissa_2042_);
v___x_2050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2050_) == 1)
{
lean_object* v_val_2051_; lean_object* v___x_2053_; 
lean_dec(v_a_2049_);
lean_del_object(v___x_2036_);
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2050_, 1);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v_x_2024_);
lean_ctor_set(v___x_2040_, 0, v_val_2051_);
v___x_2053_ = v___x_2040_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_val_2051_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_x_2024_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
v_x_2023_ = v_tail_2038_;
v_x_2024_ = v___x_2053_;
goto _start;
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec(v___x_2050_);
lean_del_object(v___x_2040_);
lean_dec(v_tail_2038_);
lean_dec_ref(v___y_2025_);
lean_dec(v_x_2024_);
v___x_2056_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2057_ = l_Nat_reprFast(v_a_2049_);
v___x_2058_ = lean_string_append(v___x_2056_, v___x_2057_);
lean_dec_ref(v___x_2057_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 18);
lean_ctor_set(v___x_2036_, 0, v___x_2058_);
v___x_2060_ = v___x_2036_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
}
}
else
{
lean_dec(v_exponent_2043_);
lean_dec(v_mantissa_2042_);
lean_del_object(v___x_2040_);
lean_dec(v_tail_2038_);
lean_del_object(v___x_2036_);
lean_dec_ref(v___y_2025_);
lean_dec(v_x_2024_);
goto v___jp_2027_;
}
}
}
}
else
{
lean_dec(v_head_2033_);
lean_dec_ref_known(v_x_2023_, 2);
lean_dec_ref(v___y_2025_);
lean_dec(v_x_2024_);
goto v___jp_2027_;
}
}
v___jp_2027_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___closed__1));
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0___boxed(lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v_x_2066_, v_x_2067_, v___y_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(lean_object* v_idxs_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_array_to_list(v_idxs_2071_);
v___x_2075_ = lean_box(0);
v___x_2076_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_getNameList_spec__0(v___x_2074_, v___x_2075_, v_a_2072_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList___boxed(lean_object* v_idxs_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_idxs_2077_, v_a_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(lean_object* v_a_2081_, lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2082_) == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = 0;
return v___x_2083_;
}
else
{
lean_object* v_key_2084_; lean_object* v_tail_2085_; uint8_t v___x_2086_; 
v_key_2084_ = lean_ctor_get(v_x_2082_, 0);
v_tail_2085_ = lean_ctor_get(v_x_2082_, 2);
v___x_2086_ = lean_name_eq(v_key_2084_, v_a_2081_);
if (v___x_2086_ == 0)
{
v_x_2082_ = v_tail_2085_;
goto _start;
}
else
{
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
uint8_t v_res_2090_; lean_object* v_r_2091_; 
v_res_2090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2088_, v_x_2089_);
lean_dec(v_x_2089_);
lean_dec(v_a_2088_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(lean_object* v_m_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_buckets_2094_; lean_object* v___x_2095_; uint64_t v___y_2097_; 
v_buckets_2094_ = lean_ctor_get(v_m_2092_, 1);
v___x_2095_ = lean_array_get_size(v_buckets_2094_);
if (lean_obj_tag(v_a_2093_) == 0)
{
uint64_t v___x_2111_; 
v___x_2111_ = 1723ULL;
v___y_2097_ = v___x_2111_;
goto v___jp_2096_;
}
else
{
uint64_t v_hash_2112_; 
v_hash_2112_ = lean_ctor_get_uint64(v_a_2093_, sizeof(void*)*2);
v___y_2097_ = v_hash_2112_;
goto v___jp_2096_;
}
v___jp_2096_:
{
uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v_fold_2100_; uint64_t v___x_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2098_ = 32ULL;
v___x_2099_ = lean_uint64_shift_right(v___y_2097_, v___x_2098_);
v_fold_2100_ = lean_uint64_xor(v___y_2097_, v___x_2099_);
v___x_2101_ = 16ULL;
v___x_2102_ = lean_uint64_shift_right(v_fold_2100_, v___x_2101_);
v___x_2103_ = lean_uint64_xor(v_fold_2100_, v___x_2102_);
v___x_2104_ = lean_uint64_to_usize(v___x_2103_);
v___x_2105_ = lean_usize_of_nat(v___x_2095_);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_sub(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_usize_land(v___x_2104_, v___x_2107_);
v___x_2109_ = lean_array_uget_borrowed(v_buckets_2094_, v___x_2108_);
v___x_2110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2093_, v___x_2109_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg___boxed(lean_object* v_m_2113_, lean_object* v_a_2114_){
_start:
{
uint8_t v_res_2115_; lean_object* v_r_2116_; 
v_res_2115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_m_2113_);
v_r_2116_ = lean_box(v_res_2115_);
return v_r_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
return v_x_2117_;
}
else
{
lean_object* v_key_2119_; lean_object* v_value_2120_; lean_object* v_tail_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2147_; 
v_key_2119_ = lean_ctor_get(v_x_2118_, 0);
v_value_2120_ = lean_ctor_get(v_x_2118_, 1);
v_tail_2121_ = lean_ctor_get(v_x_2118_, 2);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2123_ = v_x_2118_;
v_isShared_2124_ = v_isSharedCheck_2147_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_tail_2121_);
lean_inc(v_value_2120_);
lean_inc(v_key_2119_);
lean_dec(v_x_2118_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2147_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; uint64_t v___y_2127_; 
v___x_2125_ = lean_array_get_size(v_x_2117_);
if (lean_obj_tag(v_key_2119_) == 0)
{
uint64_t v___x_2145_; 
v___x_2145_ = 1723ULL;
v___y_2127_ = v___x_2145_;
goto v___jp_2126_;
}
else
{
uint64_t v_hash_2146_; 
v_hash_2146_ = lean_ctor_get_uint64(v_key_2119_, sizeof(void*)*2);
v___y_2127_ = v_hash_2146_;
goto v___jp_2126_;
}
v___jp_2126_:
{
uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v_fold_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2128_ = 32ULL;
v___x_2129_ = lean_uint64_shift_right(v___y_2127_, v___x_2128_);
v_fold_2130_ = lean_uint64_xor(v___y_2127_, v___x_2129_);
v___x_2131_ = 16ULL;
v___x_2132_ = lean_uint64_shift_right(v_fold_2130_, v___x_2131_);
v___x_2133_ = lean_uint64_xor(v_fold_2130_, v___x_2132_);
v___x_2134_ = lean_uint64_to_usize(v___x_2133_);
v___x_2135_ = lean_usize_of_nat(v___x_2125_);
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_sub(v___x_2135_, v___x_2136_);
v___x_2138_ = lean_usize_land(v___x_2134_, v___x_2137_);
v___x_2139_ = lean_array_uget_borrowed(v_x_2117_, v___x_2138_);
lean_inc(v___x_2139_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 2, v___x_2139_);
v___x_2141_ = v___x_2123_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_key_2119_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_value_2120_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_array_uset(v_x_2117_, v___x_2138_, v___x_2141_);
v_x_2117_ = v___x_2142_;
v_x_2118_ = v_tail_2121_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2148_, lean_object* v_source_2149_, lean_object* v_target_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = lean_array_get_size(v_source_2149_);
v___x_2152_ = lean_nat_dec_lt(v_i_2148_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v_source_2149_);
lean_dec(v_i_2148_);
return v_target_2150_;
}
else
{
lean_object* v_es_2153_; lean_object* v___x_2154_; lean_object* v_source_2155_; lean_object* v_target_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_es_2153_ = lean_array_fget(v_source_2149_, v_i_2148_);
v___x_2154_ = lean_box(0);
v_source_2155_ = lean_array_fset(v_source_2149_, v_i_2148_, v___x_2154_);
v_target_2156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2150_, v_es_2153_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_add(v_i_2148_, v___x_2157_);
lean_dec(v_i_2148_);
v_i_2148_ = v___x_2158_;
v_source_2149_ = v_source_2155_;
v_target_2150_ = v_target_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(lean_object* v_data_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_nbuckets_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2161_ = lean_array_get_size(v_data_2160_);
v___x_2162_ = lean_unsigned_to_nat(2u);
v_nbuckets_2163_ = lean_nat_mul(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_mk_array(v_nbuckets_2163_, v___x_2165_);
v___x_2167_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v___x_2164_, v_data_2160_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(lean_object* v_a_2168_, lean_object* v_b_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 0)
{
lean_dec(v_b_2169_);
lean_dec(v_a_2168_);
return v_x_2170_;
}
else
{
lean_object* v_key_2171_; lean_object* v_value_2172_; lean_object* v_tail_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_key_2171_ = lean_ctor_get(v_x_2170_, 0);
v_value_2172_ = lean_ctor_get(v_x_2170_, 1);
v_tail_2173_ = lean_ctor_get(v_x_2170_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_x_2170_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v_x_2170_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_tail_2173_);
lean_inc(v_value_2172_);
lean_inc(v_key_2171_);
lean_dec(v_x_2170_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_name_eq(v_key_2171_, v_a_2168_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2168_, v_b_2169_, v_tail_2173_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 2, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_key_2171_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_value_2172_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2183_; 
lean_dec(v_value_2172_);
lean_dec(v_key_2171_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_b_2169_);
lean_ctor_set(v___x_2175_, 0, v_a_2168_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2168_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_b_2169_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_tail_2173_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(lean_object* v_m_2186_, lean_object* v_a_2187_, lean_object* v_b_2188_){
_start:
{
lean_object* v_size_2189_; lean_object* v_buckets_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2236_; 
v_size_2189_ = lean_ctor_get(v_m_2186_, 0);
v_buckets_2190_ = lean_ctor_get(v_m_2186_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_m_2186_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2192_ = v_m_2186_;
v_isShared_2193_ = v_isSharedCheck_2236_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_buckets_2190_);
lean_inc(v_size_2189_);
lean_dec(v_m_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2236_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; uint64_t v___y_2196_; 
v___x_2194_ = lean_array_get_size(v_buckets_2190_);
if (lean_obj_tag(v_a_2187_) == 0)
{
uint64_t v___x_2234_; 
v___x_2234_ = 1723ULL;
v___y_2196_ = v___x_2234_;
goto v___jp_2195_;
}
else
{
uint64_t v_hash_2235_; 
v_hash_2235_ = lean_ctor_get_uint64(v_a_2187_, sizeof(void*)*2);
v___y_2196_ = v_hash_2235_;
goto v___jp_2195_;
}
v___jp_2195_:
{
uint64_t v___x_2197_; uint64_t v___x_2198_; uint64_t v_fold_2199_; uint64_t v___x_2200_; uint64_t v___x_2201_; uint64_t v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v_bkt_2208_; uint8_t v___x_2209_; 
v___x_2197_ = 32ULL;
v___x_2198_ = lean_uint64_shift_right(v___y_2196_, v___x_2197_);
v_fold_2199_ = lean_uint64_xor(v___y_2196_, v___x_2198_);
v___x_2200_ = 16ULL;
v___x_2201_ = lean_uint64_shift_right(v_fold_2199_, v___x_2200_);
v___x_2202_ = lean_uint64_xor(v_fold_2199_, v___x_2201_);
v___x_2203_ = lean_uint64_to_usize(v___x_2202_);
v___x_2204_ = lean_usize_of_nat(v___x_2194_);
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_sub(v___x_2204_, v___x_2205_);
v___x_2207_ = lean_usize_land(v___x_2203_, v___x_2206_);
v_bkt_2208_ = lean_array_uget_borrowed(v_buckets_2190_, v___x_2207_);
v___x_2209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2187_, v_bkt_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v_size_x27_2211_; lean_object* v___x_2212_; lean_object* v_buckets_x27_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2210_ = lean_unsigned_to_nat(1u);
v_size_x27_2211_ = lean_nat_add(v_size_2189_, v___x_2210_);
lean_dec(v_size_2189_);
lean_inc(v_bkt_2208_);
v___x_2212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2187_);
lean_ctor_set(v___x_2212_, 1, v_b_2188_);
lean_ctor_set(v___x_2212_, 2, v_bkt_2208_);
v_buckets_x27_2213_ = lean_array_uset(v_buckets_2190_, v___x_2207_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(4u);
v___x_2215_ = lean_nat_mul(v_size_x27_2211_, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(3u);
v___x_2217_ = lean_nat_div(v___x_2215_, v___x_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_array_get_size(v_buckets_x27_2213_);
v___x_2219_ = lean_nat_dec_le(v___x_2217_, v___x_2218_);
lean_dec(v___x_2217_);
if (v___x_2219_ == 0)
{
lean_object* v_val_2220_; lean_object* v___x_2222_; 
v_val_2220_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_buckets_x27_2213_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v_val_2220_);
lean_ctor_set(v___x_2192_, 0, v_size_x27_2211_);
v___x_2222_ = v___x_2192_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_size_x27_2211_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_val_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_object* v___x_2225_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v_buckets_x27_2213_);
lean_ctor_set(v___x_2192_, 0, v_size_x27_2211_);
v___x_2225_ = v___x_2192_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_size_x27_2211_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_buckets_x27_2213_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v_buckets_x27_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
lean_inc(v_bkt_2208_);
v___x_2227_ = lean_box(0);
v_buckets_x27_2228_ = lean_array_uset(v_buckets_2190_, v___x_2207_, v___x_2227_);
v___x_2229_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2187_, v_b_2188_, v_bkt_2208_);
v___x_2230_ = lean_array_uset(v_buckets_x27_2228_, v___x_2207_, v___x_2229_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2230_);
v___x_2232_ = v___x_2192_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_size_2189_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(lean_object* v_data_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2242_, v___x_2257_);
if (lean_obj_tag(v___x_2258_) == 1)
{
lean_object* v_val_2259_; 
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v___x_2258_, 1);
if (lean_obj_tag(v_val_2259_) == 2)
{
lean_object* v_n_2260_; lean_object* v_mantissa_2261_; lean_object* v_exponent_2262_; lean_object* v_natZero_2263_; lean_object* v_intZero_2264_; uint8_t v_isNeg_2265_; 
v_n_2260_ = lean_ctor_get(v_val_2259_, 0);
lean_inc_ref(v_n_2260_);
lean_dec_ref_known(v_val_2259_, 1);
v_mantissa_2261_ = lean_ctor_get(v_n_2260_, 0);
lean_inc(v_mantissa_2261_);
v_exponent_2262_ = lean_ctor_get(v_n_2260_, 1);
lean_inc(v_exponent_2262_);
lean_dec_ref(v_n_2260_);
v_natZero_2263_ = lean_unsigned_to_nat(0u);
v_intZero_2264_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2265_ = lean_int_dec_lt(v_mantissa_2261_, v_intZero_2264_);
if (v_isNeg_2265_ == 0)
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_nat_dec_eq(v_exponent_2262_, v_natZero_2263_);
lean_dec(v_exponent_2262_);
if (v___x_2266_ == 0)
{
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2245_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2242_, v___x_2267_);
if (lean_obj_tag(v___x_2268_) == 1)
{
lean_object* v_val_2269_; 
v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v___x_2268_, 1);
if (lean_obj_tag(v_val_2269_) == 4)
{
lean_object* v_elems_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_elems_2270_ = lean_ctor_get(v_val_2269_, 0);
lean_inc_ref(v_elems_2270_);
lean_dec_ref_known(v_val_2269_, 1);
v___x_2271_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2242_, v___x_2271_);
if (lean_obj_tag(v___x_2272_) == 1)
{
lean_object* v_val_2273_; 
v_val_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v___x_2272_, 1);
if (lean_obj_tag(v_val_2273_) == 2)
{
lean_object* v_n_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2381_; 
v_n_2274_ = lean_ctor_get(v_val_2273_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_val_2273_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2276_ = v_val_2273_;
v_isShared_2277_ = v_isSharedCheck_2381_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_n_2274_);
lean_dec(v_val_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2381_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_mantissa_2278_; lean_object* v_exponent_2279_; uint8_t v_isNeg_2280_; 
v_mantissa_2278_ = lean_ctor_get(v_n_2274_, 0);
lean_inc(v_mantissa_2278_);
v_exponent_2279_ = lean_ctor_get(v_n_2274_, 1);
lean_inc(v_exponent_2279_);
lean_dec_ref(v_n_2274_);
v_isNeg_2280_ = lean_int_dec_lt(v_mantissa_2278_, v_intZero_2264_);
if (v_isNeg_2280_ == 0)
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_nat_dec_eq(v_exponent_2279_, v_natZero_2263_);
lean_dec(v_exponent_2279_);
if (v___x_2281_ == 0)
{
lean_dec(v_mantissa_2278_);
lean_del_object(v___x_2276_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2251_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_2283_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2242_, v___x_2282_);
if (lean_obj_tag(v___x_2283_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2380_; 
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2380_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2380_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
if (lean_obj_tag(v_val_2284_) == 1)
{
uint8_t v_b_2288_; lean_object* v_nameMap_2289_; lean_object* v_a_2290_; lean_object* v___x_2291_; 
v_b_2288_ = lean_ctor_get_uint8(v_val_2284_, 0);
lean_dec_ref_known(v_val_2284_, 0);
v_nameMap_2289_ = lean_ctor_get(v_a_2243_, 1);
v_a_2290_ = lean_nat_abs(v_mantissa_2261_);
lean_dec(v_mantissa_2261_);
v___x_2291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2291_) == 1)
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_a_2290_);
lean_del_object(v___x_2286_);
lean_del_object(v___x_2276_);
v_val_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2370_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2370_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2270_, v_a_2243_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2361_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2361_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2361_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_snd_2301_; lean_object* v_fst_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2360_; 
v_snd_2301_ = lean_ctor_get(v_a_2297_, 1);
v_fst_2302_ = lean_ctor_get(v_a_2297_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_a_2297_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2304_ = v_a_2297_;
v_isShared_2305_ = v_isSharedCheck_2360_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snd_2301_);
lean_inc(v_fst_2302_);
lean_dec(v_a_2297_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2360_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_stream_2306_; lean_object* v_nameMap_2307_; lean_object* v_levelMap_2308_; lean_object* v_exprMap_2309_; lean_object* v_recursorRuleMap_2310_; lean_object* v_constMap_2311_; lean_object* v_constOrder_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2359_; 
v_stream_2306_ = lean_ctor_get(v_snd_2301_, 0);
v_nameMap_2307_ = lean_ctor_get(v_snd_2301_, 1);
v_levelMap_2308_ = lean_ctor_get(v_snd_2301_, 2);
v_exprMap_2309_ = lean_ctor_get(v_snd_2301_, 3);
v_recursorRuleMap_2310_ = lean_ctor_get(v_snd_2301_, 4);
v_constMap_2311_ = lean_ctor_get(v_snd_2301_, 5);
v_constOrder_2312_ = lean_ctor_get(v_snd_2301_, 6);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_snd_2301_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2314_ = v_snd_2301_;
v_isShared_2315_ = v_isSharedCheck_2359_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_constOrder_2312_);
lean_inc(v_constMap_2311_);
lean_inc(v_recursorRuleMap_2310_);
lean_inc(v_exprMap_2309_);
lean_inc(v_levelMap_2308_);
lean_inc(v_nameMap_2307_);
lean_inc(v_stream_2306_);
lean_dec(v_snd_2301_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2359_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_nat_abs(v_mantissa_2278_);
lean_dec(v_mantissa_2278_);
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2309_, v_a_2316_);
if (lean_obj_tag(v___x_2317_) == 1)
{
lean_object* v_val_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2316_);
lean_del_object(v___x_2294_);
v_val_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2349_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_val_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2349_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
lean_inc(v_val_2292_);
v___x_2322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2322_, 0, v_val_2292_);
lean_ctor_set(v___x_2322_, 1, v_fst_2302_);
lean_ctor_set(v___x_2322_, 2, v_val_2318_);
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2311_, v_val_2292_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*1, v_b_2288_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2324_);
v___x_2326_ = v___x_2320_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2327_ = lean_box(0);
lean_inc(v_val_2292_);
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2311_, v_val_2292_, v___x_2326_);
v___x_2329_ = lean_array_push(v_constOrder_2312_, v_val_2292_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 6, v___x_2329_);
lean_ctor_set(v___x_2314_, 5, v___x_2328_);
v___x_2331_ = v___x_2314_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_stream_2306_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nameMap_2307_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_levelMap_2308_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_exprMap_2309_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v_recursorRuleMap_2310_);
lean_ctor_set(v_reuseFailAlloc_2338_, 5, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2338_, 6, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2331_);
lean_ctor_set(v___x_2304_, 0, v___x_2327_);
v___x_2333_ = v___x_2304_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2333_);
v___x_2335_ = v___x_2299_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
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
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref_known(v___x_2322_, 3);
lean_del_object(v___x_2314_);
lean_dec_ref(v_constOrder_2312_);
lean_dec_ref(v_constMap_2311_);
lean_dec_ref(v_recursorRuleMap_2310_);
lean_dec_ref(v_exprMap_2309_);
lean_dec_ref(v_levelMap_2308_);
lean_dec_ref(v_nameMap_2307_);
lean_dec_ref(v_stream_2306_);
lean_del_object(v___x_2304_);
v___x_2340_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2292_, v___x_2323_);
v___x_2342_ = lean_string_append(v___x_2340_, v___x_2341_);
lean_dec_ref(v___x_2341_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 18);
lean_ctor_set(v___x_2320_, 0, v___x_2342_);
v___x_2344_ = v___x_2320_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 1);
lean_ctor_set(v___x_2299_, 0, v___x_2344_);
v___x_2346_ = v___x_2299_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec(v___x_2317_);
lean_del_object(v___x_2314_);
lean_dec_ref(v_constOrder_2312_);
lean_dec_ref(v_constMap_2311_);
lean_dec_ref(v_recursorRuleMap_2310_);
lean_dec_ref(v_exprMap_2309_);
lean_dec_ref(v_levelMap_2308_);
lean_dec_ref(v_nameMap_2307_);
lean_dec_ref(v_stream_2306_);
lean_del_object(v___x_2304_);
lean_dec(v_fst_2302_);
lean_dec(v_val_2292_);
v___x_2350_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2351_ = l_Nat_reprFast(v_a_2316_);
v___x_2352_ = lean_string_append(v___x_2350_, v___x_2351_);
lean_dec_ref(v___x_2351_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 18);
lean_ctor_set(v___x_2294_, 0, v___x_2352_);
v___x_2354_ = v___x_2294_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 1);
lean_ctor_set(v___x_2299_, 0, v___x_2354_);
v___x_2356_ = v___x_2299_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2294_);
lean_dec(v_val_2292_);
lean_dec(v_mantissa_2278_);
v_a_2362_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2296_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2296_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec(v___x_2291_);
lean_dec(v_mantissa_2278_);
lean_dec_ref(v_elems_2270_);
lean_dec_ref(v_a_2243_);
v___x_2371_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2372_ = l_Nat_reprFast(v_a_2290_);
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
lean_dec_ref(v___x_2372_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 18);
lean_ctor_set(v___x_2286_, 0, v___x_2373_);
v___x_2375_ = v___x_2286_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 1);
lean_ctor_set(v___x_2276_, 0, v___x_2375_);
v___x_2377_ = v___x_2276_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_del_object(v___x_2286_);
lean_dec(v_val_2284_);
lean_dec(v_mantissa_2278_);
lean_del_object(v___x_2276_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2254_;
}
}
}
else
{
lean_dec(v___x_2283_);
lean_dec(v_mantissa_2278_);
lean_del_object(v___x_2276_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2254_;
}
}
}
else
{
lean_dec(v_exponent_2279_);
lean_dec(v_mantissa_2278_);
lean_del_object(v___x_2276_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2251_;
}
}
}
else
{
lean_dec(v_val_2273_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2251_;
}
}
else
{
lean_dec(v___x_2272_);
lean_dec_ref(v_elems_2270_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2251_;
}
}
else
{
lean_dec(v_val_2269_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2248_;
}
}
else
{
lean_dec(v___x_2268_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2248_;
}
}
}
else
{
lean_dec(v_exponent_2262_);
lean_dec(v_mantissa_2261_);
lean_dec_ref(v_a_2243_);
goto v___jp_2245_;
}
}
else
{
lean_dec(v_val_2259_);
lean_dec_ref(v_a_2243_);
goto v___jp_2245_;
}
}
else
{
lean_dec(v___x_2258_);
lean_dec_ref(v_a_2243_);
goto v___jp_2245_;
}
v___jp_2245_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
v___jp_2248_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
v___jp_2251_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
v___jp_2254_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
v___x_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___boxed(lean_object* v_data_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_data_2382_, v_a_2383_);
lean_dec(v_data_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(lean_object* v_00_u03b2_2386_, lean_object* v_m_2387_, lean_object* v_a_2388_){
_start:
{
uint8_t v___x_2389_; 
v___x_2389_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_m_2387_, v_a_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___boxed(lean_object* v_00_u03b2_2390_, lean_object* v_m_2391_, lean_object* v_a_2392_){
_start:
{
uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_res_2393_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0(v_00_u03b2_2390_, v_m_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_m_2391_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1(lean_object* v_00_u03b2_2395_, lean_object* v_m_2396_, lean_object* v_a_2397_, lean_object* v_b_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_m_2396_, v_a_2397_, v_b_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(lean_object* v_00_u03b2_2400_, lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___redArg(v_a_2401_, v_x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2404_, lean_object* v_a_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0_spec__0(v_00_u03b2_2404_, v_a_2405_, v_x_2406_);
lean_dec(v_x_2406_);
lean_dec(v_a_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2(lean_object* v_00_u03b2_2409_, lean_object* v_data_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2___redArg(v_data_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3(lean_object* v_00_u03b2_2412_, lean_object* v_a_2413_, lean_object* v_b_2414_, lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__3___redArg(v_a_2413_, v_b_2414_, v_x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2417_, lean_object* v_i_2418_, lean_object* v_source_2419_, lean_object* v_target_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3___redArg(v_i_2418_, v_source_2419_, v_target_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2423_, v_x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(lean_object* v_data_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2466_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v_val_2468_; 
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v___x_2467_, 1);
if (lean_obj_tag(v_val_2468_) == 2)
{
lean_object* v_n_2469_; lean_object* v_mantissa_2470_; lean_object* v_exponent_2471_; lean_object* v_natZero_2472_; lean_object* v_intZero_2473_; uint8_t v_isNeg_2474_; 
v_n_2469_ = lean_ctor_get(v_val_2468_, 0);
lean_inc_ref(v_n_2469_);
lean_dec_ref_known(v_val_2468_, 1);
v_mantissa_2470_ = lean_ctor_get(v_n_2469_, 0);
lean_inc(v_mantissa_2470_);
v_exponent_2471_ = lean_ctor_get(v_n_2469_, 1);
lean_inc(v_exponent_2471_);
lean_dec_ref(v_n_2469_);
v_natZero_2472_ = lean_unsigned_to_nat(0u);
v_intZero_2473_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2474_ = lean_int_dec_lt(v_mantissa_2470_, v_intZero_2473_);
if (v_isNeg_2474_ == 0)
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_nat_dec_eq(v_exponent_2471_, v_natZero_2472_);
lean_dec(v_exponent_2471_);
if (v___x_2475_ == 0)
{
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2442_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2476_);
if (lean_obj_tag(v___x_2477_) == 1)
{
lean_object* v_val_2478_; 
v_val_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v___x_2477_, 1);
if (lean_obj_tag(v_val_2478_) == 4)
{
lean_object* v_elems_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_elems_2479_ = lean_ctor_get(v_val_2478_, 0);
lean_inc_ref(v_elems_2479_);
lean_dec_ref_known(v_val_2478_, 1);
v___x_2480_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 1)
{
lean_object* v_val_2482_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
if (lean_obj_tag(v_val_2482_) == 2)
{
lean_object* v_n_2483_; lean_object* v_mantissa_2484_; lean_object* v_exponent_2485_; uint8_t v_isNeg_2486_; 
v_n_2483_ = lean_ctor_get(v_val_2482_, 0);
lean_inc_ref(v_n_2483_);
lean_dec_ref_known(v_val_2482_, 1);
v_mantissa_2484_ = lean_ctor_get(v_n_2483_, 0);
lean_inc(v_mantissa_2484_);
v_exponent_2485_ = lean_ctor_get(v_n_2483_, 1);
lean_inc(v_exponent_2485_);
lean_dec_ref(v_n_2483_);
v_isNeg_2486_ = lean_int_dec_lt(v_mantissa_2484_, v_intZero_2473_);
if (v_isNeg_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_nat_dec_eq(v_exponent_2485_, v_natZero_2472_);
lean_dec(v_exponent_2485_);
if (v___x_2487_ == 0)
{
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2448_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 1)
{
lean_object* v_val_2490_; 
v_val_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2489_, 1);
if (lean_obj_tag(v_val_2490_) == 2)
{
lean_object* v_n_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2689_; 
v_n_2491_ = lean_ctor_get(v_val_2490_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_val_2490_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2493_ = v_val_2490_;
v_isShared_2494_ = v_isSharedCheck_2689_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_n_2491_);
lean_dec(v_val_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2689_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_mantissa_2495_; lean_object* v_exponent_2496_; uint8_t v_isNeg_2497_; 
v_mantissa_2495_ = lean_ctor_get(v_n_2491_, 0);
lean_inc(v_mantissa_2495_);
v_exponent_2496_ = lean_ctor_get(v_n_2491_, 1);
lean_inc(v_exponent_2496_);
lean_dec_ref(v_n_2491_);
v_isNeg_2497_ = lean_int_dec_lt(v_mantissa_2495_, v_intZero_2473_);
if (v_isNeg_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_nat_dec_eq(v_exponent_2496_, v_natZero_2472_);
lean_dec(v_exponent_2496_);
if (v___x_2498_ == 0)
{
lean_dec(v_mantissa_2495_);
lean_del_object(v___x_2493_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2451_;
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__2));
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2499_);
if (lean_obj_tag(v___x_2500_) == 1)
{
lean_object* v_val_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_del_object(v___x_2493_);
v_val_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__3));
v___x_2503_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2502_);
if (lean_obj_tag(v___x_2503_) == 1)
{
lean_object* v_val_2504_; 
v_val_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_val_2504_);
lean_dec_ref_known(v___x_2503_, 1);
if (lean_obj_tag(v_val_2504_) == 3)
{
lean_object* v_s_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_s_2505_ = lean_ctor_get(v_val_2504_, 0);
lean_inc_ref(v_s_2505_);
lean_dec_ref_known(v_val_2504_, 1);
v___x_2506_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2439_, v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 1)
{
lean_object* v_val_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2684_; 
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2684_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_val_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2684_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
if (lean_obj_tag(v_val_2508_) == 4)
{
lean_object* v_elems_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2683_; 
v_elems_2512_ = lean_ctor_get(v_val_2508_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_val_2508_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2514_ = v_val_2508_;
v_isShared_2515_ = v_isSharedCheck_2683_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_elems_2512_);
lean_dec(v_val_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2683_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v_nameMap_2516_; lean_object* v_a_2517_; lean_object* v___x_2518_; 
v_nameMap_2516_ = lean_ctor_get(v_a_2440_, 1);
v_a_2517_ = lean_nat_abs(v_mantissa_2470_);
lean_dec(v_mantissa_2470_);
v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_a_2517_);
lean_del_object(v___x_2514_);
lean_del_object(v___x_2510_);
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2673_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_val_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2673_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2479_, v_a_2440_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2664_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2664_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2664_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_snd_2528_; lean_object* v_fst_2529_; lean_object* v_exprMap_2530_; lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_snd_2528_ = lean_ctor_get(v_a_2524_, 1);
lean_inc(v_snd_2528_);
v_fst_2529_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_fst_2529_);
lean_dec(v_a_2524_);
v_exprMap_2530_ = lean_ctor_get(v_snd_2528_, 3);
v_a_2531_ = lean_nat_abs(v_mantissa_2484_);
lean_dec(v_mantissa_2484_);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2532_) == 1)
{
lean_object* v_val_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_a_2531_);
lean_del_object(v___x_2521_);
v_val_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2654_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_val_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2654_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
v_a_2537_ = lean_nat_abs(v_mantissa_2495_);
lean_dec(v_mantissa_2495_);
v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2530_, v_a_2537_);
if (lean_obj_tag(v___x_2538_) == 1)
{
lean_object* v_val_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2537_);
v_val_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2644_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_val_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2644_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___y_2544_; uint8_t v_safety_2545_; lean_object* v___y_2546_; lean_object* v_hints_2606_; lean_object* v___y_2607_; 
switch(lean_obj_tag(v_val_2501_))
{
case 3:
{
lean_object* v_s_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_s_2625_ = lean_ctor_get(v_val_2501_, 0);
lean_inc_ref(v_s_2625_);
lean_dec_ref_known(v_val_2501_, 1);
v___x_2626_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_2627_ = lean_string_dec_eq(v_s_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__10));
v___x_2629_ = lean_string_dec_eq(v_s_2625_, v___x_2628_);
lean_dec_ref(v_s_2625_);
if (v___x_2629_ == 0)
{
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
goto v___jp_2460_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_box(1);
v_hints_2606_ = v___x_2630_;
v___y_2607_ = v_snd_2528_;
goto v___jp_2605_;
}
}
else
{
lean_object* v___x_2631_; 
lean_dec_ref(v_s_2625_);
v___x_2631_ = lean_box(0);
v_hints_2606_ = v___x_2631_;
v___y_2607_ = v_snd_2528_;
goto v___jp_2605_;
}
}
case 5:
{
lean_object* v_kvPairs_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v_kvPairs_2632_ = lean_ctor_get(v_val_2501_, 0);
lean_inc(v_kvPairs_2632_);
lean_dec_ref_known(v_val_2501_, 1);
v___x_2633_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__11));
v___x_2634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_2632_, v___x_2633_);
lean_dec(v_kvPairs_2632_);
if (lean_obj_tag(v___x_2634_) == 1)
{
lean_object* v_val_2635_; 
v_val_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v___x_2634_, 1);
if (lean_obj_tag(v_val_2635_) == 2)
{
lean_object* v_n_2636_; lean_object* v_mantissa_2637_; lean_object* v_exponent_2638_; uint8_t v_isNeg_2639_; 
v_n_2636_ = lean_ctor_get(v_val_2635_, 0);
lean_inc_ref(v_n_2636_);
lean_dec_ref_known(v_val_2635_, 1);
v_mantissa_2637_ = lean_ctor_get(v_n_2636_, 0);
lean_inc(v_mantissa_2637_);
v_exponent_2638_ = lean_ctor_get(v_n_2636_, 1);
lean_inc(v_exponent_2638_);
lean_dec_ref(v_n_2636_);
v_isNeg_2639_ = lean_int_dec_lt(v_mantissa_2637_, v_intZero_2473_);
if (v_isNeg_2639_ == 0)
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_eq(v_exponent_2638_, v_natZero_2472_);
lean_dec(v_exponent_2638_);
if (v___x_2640_ == 0)
{
lean_dec(v_mantissa_2637_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
goto v___jp_2463_;
}
else
{
lean_object* v_a_2641_; uint32_t v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_nat_abs(v_mantissa_2637_);
lean_dec(v_mantissa_2637_);
v___x_2642_ = lean_uint32_of_nat(v_a_2641_);
lean_dec(v_a_2641_);
v___x_2643_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_2643_, 0, v___x_2642_);
v_hints_2606_ = v___x_2643_;
v___y_2607_ = v_snd_2528_;
goto v___jp_2605_;
}
}
else
{
lean_dec(v_exponent_2638_);
lean_dec(v_mantissa_2637_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
goto v___jp_2463_;
}
}
else
{
lean_dec(v_val_2635_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
goto v___jp_2463_;
}
}
else
{
lean_dec(v___x_2634_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
goto v___jp_2463_;
}
}
default: 
{
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_del_object(v___x_2535_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_del_object(v___x_2526_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
goto v___jp_2460_;
}
}
v___jp_2543_:
{
lean_object* v___x_2547_; 
v___x_2547_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2512_, v___y_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2596_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2596_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2596_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_snd_2552_; lean_object* v_fst_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2595_; 
v_snd_2552_ = lean_ctor_get(v_a_2548_, 1);
v_fst_2553_ = lean_ctor_get(v_a_2548_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_a_2548_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2555_ = v_a_2548_;
v_isShared_2556_ = v_isSharedCheck_2595_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snd_2552_);
lean_inc(v_fst_2553_);
lean_dec(v_a_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2595_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_stream_2557_; lean_object* v_nameMap_2558_; lean_object* v_levelMap_2559_; lean_object* v_exprMap_2560_; lean_object* v_recursorRuleMap_2561_; lean_object* v_constMap_2562_; lean_object* v_constOrder_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2594_; 
v_stream_2557_ = lean_ctor_get(v_snd_2552_, 0);
v_nameMap_2558_ = lean_ctor_get(v_snd_2552_, 1);
v_levelMap_2559_ = lean_ctor_get(v_snd_2552_, 2);
v_exprMap_2560_ = lean_ctor_get(v_snd_2552_, 3);
v_recursorRuleMap_2561_ = lean_ctor_get(v_snd_2552_, 4);
v_constMap_2562_ = lean_ctor_get(v_snd_2552_, 5);
v_constOrder_2563_ = lean_ctor_get(v_snd_2552_, 6);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_snd_2552_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2565_ = v_snd_2552_;
v_isShared_2566_ = v_isSharedCheck_2594_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_constOrder_2563_);
lean_inc(v_constMap_2562_);
lean_inc(v_recursorRuleMap_2561_);
lean_inc(v_exprMap_2560_);
lean_inc(v_levelMap_2559_);
lean_inc(v_nameMap_2558_);
lean_inc(v_stream_2557_);
lean_dec(v_snd_2552_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2594_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; 
v___x_2567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2562_, v_val_2519_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_inc(v_val_2519_);
v___x_2568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2568_, 0, v_val_2519_);
lean_ctor_set(v___x_2568_, 1, v_fst_2529_);
lean_ctor_set(v___x_2568_, 2, v_val_2533_);
v___x_2569_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v_val_2539_);
lean_ctor_set(v___x_2569_, 2, v___y_2544_);
lean_ctor_set(v___x_2569_, 3, v_fst_2553_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*4, v_safety_2545_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2569_);
v___x_2571_ = v___x_2541_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2572_ = lean_box(0);
lean_inc(v_val_2519_);
v___x_2573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2562_, v_val_2519_, v___x_2571_);
v___x_2574_ = lean_array_push(v_constOrder_2563_, v_val_2519_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 6, v___x_2574_);
lean_ctor_set(v___x_2565_, 5, v___x_2573_);
v___x_2576_ = v___x_2565_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_stream_2557_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_nameMap_2558_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_levelMap_2559_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_exprMap_2560_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_recursorRuleMap_2561_);
lean_ctor_set(v_reuseFailAlloc_2583_, 5, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2583_, 6, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2576_);
lean_ctor_set(v___x_2555_, 0, v___x_2572_);
v___x_2578_ = v___x_2555_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2578_);
v___x_2580_ = v___x_2550_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_del_object(v___x_2565_);
lean_dec_ref(v_constOrder_2563_);
lean_dec_ref(v_constMap_2562_);
lean_dec_ref(v_recursorRuleMap_2561_);
lean_dec_ref(v_exprMap_2560_);
lean_dec_ref(v_levelMap_2559_);
lean_dec_ref(v_nameMap_2558_);
lean_dec_ref(v_stream_2557_);
lean_del_object(v___x_2555_);
lean_dec(v_fst_2553_);
lean_dec(v___y_2544_);
lean_dec(v_val_2539_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
v___x_2585_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2519_, v___x_2567_);
v___x_2587_ = lean_string_append(v___x_2585_, v___x_2586_);
lean_dec_ref(v___x_2586_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 18);
lean_ctor_set(v___x_2541_, 0, v___x_2587_);
v___x_2589_ = v___x_2541_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 1);
lean_ctor_set(v___x_2550_, 0, v___x_2589_);
v___x_2591_ = v___x_2550_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v___y_2544_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_val_2519_);
v_a_2597_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2547_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2547_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
v___jp_2605_:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__5));
v___x_2609_ = lean_string_dec_eq(v_s_2505_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__6));
v___x_2611_ = lean_string_dec_eq(v_s_2505_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__7));
v___x_2613_ = lean_string_dec_eq(v_s_2505_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_dec_ref(v___y_2607_);
lean_dec(v_hints_2606_);
lean_del_object(v___x_2541_);
lean_dec(v_val_2539_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
v___x_2614_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__8));
v___x_2615_ = lean_string_append(v___x_2614_, v_s_2505_);
lean_dec_ref(v_s_2505_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 18);
lean_ctor_set(v___x_2535_, 0, v___x_2615_);
v___x_2617_ = v___x_2535_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2617_);
v___x_2619_ = v___x_2526_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
uint8_t v___x_2622_; 
lean_del_object(v___x_2535_);
lean_del_object(v___x_2526_);
lean_dec_ref(v_s_2505_);
v___x_2622_ = 2;
v___y_2544_ = v_hints_2606_;
v_safety_2545_ = v___x_2622_;
v___y_2546_ = v___y_2607_;
goto v___jp_2543_;
}
}
else
{
uint8_t v___x_2623_; 
lean_del_object(v___x_2535_);
lean_del_object(v___x_2526_);
lean_dec_ref(v_s_2505_);
v___x_2623_ = 1;
v___y_2544_ = v_hints_2606_;
v_safety_2545_ = v___x_2623_;
v___y_2546_ = v___y_2607_;
goto v___jp_2543_;
}
}
else
{
uint8_t v___x_2624_; 
lean_del_object(v___x_2535_);
lean_del_object(v___x_2526_);
lean_dec_ref(v_s_2505_);
v___x_2624_ = 0;
v___y_2544_ = v_hints_2606_;
v_safety_2545_ = v___x_2624_;
v___y_2546_ = v___y_2607_;
goto v___jp_2543_;
}
}
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec(v___x_2538_);
lean_dec(v_val_2533_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
v___x_2645_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2646_ = l_Nat_reprFast(v_a_2537_);
v___x_2647_ = lean_string_append(v___x_2645_, v___x_2646_);
lean_dec_ref(v___x_2646_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 18);
lean_ctor_set(v___x_2535_, 0, v___x_2647_);
v___x_2649_ = v___x_2535_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2649_);
v___x_2651_ = v___x_2526_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
lean_dec(v___x_2532_);
lean_dec(v_fst_2529_);
lean_dec(v_snd_2528_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
v___x_2655_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2656_ = l_Nat_reprFast(v_a_2531_);
v___x_2657_ = lean_string_append(v___x_2655_, v___x_2656_);
lean_dec_ref(v___x_2656_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 18);
lean_ctor_set(v___x_2521_, 0, v___x_2657_);
v___x_2659_ = v___x_2521_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2659_);
v___x_2661_ = v___x_2526_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
v_a_2665_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2523_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2523_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_dec(v___x_2518_);
lean_dec_ref(v_elems_2512_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec_ref(v_a_2440_);
v___x_2674_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2675_ = l_Nat_reprFast(v_a_2517_);
v___x_2676_ = lean_string_append(v___x_2674_, v___x_2675_);
lean_dec_ref(v___x_2675_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 18);
lean_ctor_set(v___x_2514_, 0, v___x_2676_);
v___x_2678_ = v___x_2514_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2678_);
v___x_2680_ = v___x_2510_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
else
{
lean_del_object(v___x_2510_);
lean_dec(v_val_2508_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2457_;
}
}
}
else
{
lean_dec(v___x_2507_);
lean_dec_ref(v_s_2505_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2457_;
}
}
else
{
lean_dec(v_val_2504_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2454_;
}
}
else
{
lean_dec(v___x_2503_);
lean_dec(v_val_2501_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2454_;
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_dec(v___x_2500_);
lean_dec(v_mantissa_2495_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
v___x_2685_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2685_);
v___x_2687_ = v___x_2493_;
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
else
{
lean_dec(v_exponent_2496_);
lean_dec(v_mantissa_2495_);
lean_del_object(v___x_2493_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2451_;
}
}
}
else
{
lean_dec(v_val_2490_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2451_;
}
}
else
{
lean_dec(v___x_2489_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2451_;
}
}
}
else
{
lean_dec(v_exponent_2485_);
lean_dec(v_mantissa_2484_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2448_;
}
}
else
{
lean_dec(v_val_2482_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2448_;
}
}
else
{
lean_dec(v___x_2481_);
lean_dec_ref(v_elems_2479_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2448_;
}
}
else
{
lean_dec(v_val_2478_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2445_;
}
}
else
{
lean_dec(v___x_2477_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2445_;
}
}
}
else
{
lean_dec(v_exponent_2471_);
lean_dec(v_mantissa_2470_);
lean_dec_ref(v_a_2440_);
goto v___jp_2442_;
}
}
else
{
lean_dec(v_val_2468_);
lean_dec_ref(v_a_2440_);
goto v___jp_2442_;
}
}
else
{
lean_dec(v___x_2467_);
lean_dec_ref(v_a_2440_);
goto v___jp_2442_;
}
v___jp_2442_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
v___jp_2445_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
v___jp_2457_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
v___jp_2460_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
v___jp_2463_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__1));
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___boxed(lean_object* v_data_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_data_2690_, v_a_2691_);
lean_dec(v_data_2690_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(lean_object* v_data_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2716_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2697_, v___x_2715_);
if (lean_obj_tag(v___x_2716_) == 1)
{
lean_object* v_val_2717_; 
v_val_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v___x_2716_, 1);
if (lean_obj_tag(v_val_2717_) == 2)
{
lean_object* v_n_2718_; lean_object* v_mantissa_2719_; lean_object* v_exponent_2720_; lean_object* v_natZero_2721_; lean_object* v_intZero_2722_; uint8_t v_isNeg_2723_; 
v_n_2718_ = lean_ctor_get(v_val_2717_, 0);
lean_inc_ref(v_n_2718_);
lean_dec_ref_known(v_val_2717_, 1);
v_mantissa_2719_ = lean_ctor_get(v_n_2718_, 0);
lean_inc(v_mantissa_2719_);
v_exponent_2720_ = lean_ctor_get(v_n_2718_, 1);
lean_inc(v_exponent_2720_);
lean_dec_ref(v_n_2718_);
v_natZero_2721_ = lean_unsigned_to_nat(0u);
v_intZero_2722_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2723_ = lean_int_dec_lt(v_mantissa_2719_, v_intZero_2722_);
if (v_isNeg_2723_ == 0)
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_nat_dec_eq(v_exponent_2720_, v_natZero_2721_);
lean_dec(v_exponent_2720_);
if (v___x_2724_ == 0)
{
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2700_;
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2726_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2697_, v___x_2725_);
if (lean_obj_tag(v___x_2726_) == 1)
{
lean_object* v_val_2727_; 
v_val_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_val_2727_);
lean_dec_ref_known(v___x_2726_, 1);
if (lean_obj_tag(v_val_2727_) == 4)
{
lean_object* v_elems_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_elems_2728_ = lean_ctor_get(v_val_2727_, 0);
lean_inc_ref(v_elems_2728_);
lean_dec_ref_known(v_val_2727_, 1);
v___x_2729_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2697_, v___x_2729_);
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
v_isNeg_2735_ = lean_int_dec_lt(v_mantissa_2733_, v_intZero_2722_);
if (v_isNeg_2735_ == 0)
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_nat_dec_eq(v_exponent_2734_, v_natZero_2721_);
lean_dec(v_exponent_2734_);
if (v___x_2736_ == 0)
{
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2706_;
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2697_, v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 1)
{
lean_object* v_val_2739_; 
v_val_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v___x_2738_, 1);
if (lean_obj_tag(v_val_2739_) == 2)
{
lean_object* v_n_2740_; lean_object* v_mantissa_2741_; lean_object* v_exponent_2742_; uint8_t v_isNeg_2743_; 
v_n_2740_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_n_2740_);
lean_dec_ref_known(v_val_2739_, 1);
v_mantissa_2741_ = lean_ctor_get(v_n_2740_, 0);
lean_inc(v_mantissa_2741_);
v_exponent_2742_ = lean_ctor_get(v_n_2740_, 1);
lean_inc(v_exponent_2742_);
lean_dec_ref(v_n_2740_);
v_isNeg_2743_ = lean_int_dec_lt(v_mantissa_2741_, v_intZero_2722_);
if (v_isNeg_2743_ == 0)
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_nat_dec_eq(v_exponent_2742_, v_natZero_2721_);
lean_dec(v_exponent_2742_);
if (v___x_2744_ == 0)
{
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2709_;
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2697_, v___x_2745_);
if (lean_obj_tag(v___x_2746_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2880_; 
v_val_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2880_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_val_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2880_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
if (lean_obj_tag(v_val_2747_) == 4)
{
lean_object* v_elems_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2879_; 
v_elems_2751_ = lean_ctor_get(v_val_2747_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_val_2747_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2753_ = v_val_2747_;
v_isShared_2754_ = v_isSharedCheck_2879_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_elems_2751_);
lean_dec(v_val_2747_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2879_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_nameMap_2755_; lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_nameMap_2755_ = lean_ctor_get(v_a_2698_, 1);
v_a_2756_ = lean_nat_abs(v_mantissa_2719_);
lean_dec(v_mantissa_2719_);
v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2757_) == 1)
{
lean_object* v_val_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_a_2756_);
lean_del_object(v___x_2753_);
lean_del_object(v___x_2749_);
v_val_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2869_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_val_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2869_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2728_, v_a_2698_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2860_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2860_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2860_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_snd_2767_; lean_object* v_fst_2768_; lean_object* v_exprMap_2769_; lean_object* v_a_2770_; lean_object* v___x_2771_; 
v_snd_2767_ = lean_ctor_get(v_a_2763_, 1);
lean_inc(v_snd_2767_);
v_fst_2768_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_fst_2768_);
lean_dec(v_a_2763_);
v_exprMap_2769_ = lean_ctor_get(v_snd_2767_, 3);
v_a_2770_ = lean_nat_abs(v_mantissa_2733_);
lean_dec(v_mantissa_2733_);
v___x_2771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2771_) == 1)
{
lean_object* v_val_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2770_);
lean_del_object(v___x_2760_);
v_val_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2850_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_val_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2850_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_nat_abs(v_mantissa_2741_);
lean_dec(v_mantissa_2741_);
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2769_, v_a_2776_);
if (lean_obj_tag(v___x_2777_) == 1)
{
lean_object* v_val_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2776_);
lean_del_object(v___x_2774_);
lean_del_object(v___x_2765_);
v_val_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2840_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_val_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2840_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2751_, v_snd_2767_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2831_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2831_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2831_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_snd_2787_; lean_object* v_fst_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2830_; 
v_snd_2787_ = lean_ctor_get(v_a_2783_, 1);
v_fst_2788_ = lean_ctor_get(v_a_2783_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2790_ = v_a_2783_;
v_isShared_2791_ = v_isSharedCheck_2830_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_snd_2787_);
lean_inc(v_fst_2788_);
lean_dec(v_a_2783_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2830_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_stream_2792_; lean_object* v_nameMap_2793_; lean_object* v_levelMap_2794_; lean_object* v_exprMap_2795_; lean_object* v_recursorRuleMap_2796_; lean_object* v_constMap_2797_; lean_object* v_constOrder_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2829_; 
v_stream_2792_ = lean_ctor_get(v_snd_2787_, 0);
v_nameMap_2793_ = lean_ctor_get(v_snd_2787_, 1);
v_levelMap_2794_ = lean_ctor_get(v_snd_2787_, 2);
v_exprMap_2795_ = lean_ctor_get(v_snd_2787_, 3);
v_recursorRuleMap_2796_ = lean_ctor_get(v_snd_2787_, 4);
v_constMap_2797_ = lean_ctor_get(v_snd_2787_, 5);
v_constOrder_2798_ = lean_ctor_get(v_snd_2787_, 6);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_snd_2787_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2800_ = v_snd_2787_;
v_isShared_2801_ = v_isSharedCheck_2829_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_constOrder_2798_);
lean_inc(v_constMap_2797_);
lean_inc(v_recursorRuleMap_2796_);
lean_inc(v_exprMap_2795_);
lean_inc(v_levelMap_2794_);
lean_inc(v_nameMap_2793_);
lean_inc(v_stream_2792_);
lean_dec(v_snd_2787_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2829_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
uint8_t v___x_2802_; 
v___x_2802_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2797_, v_val_2758_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_inc(v_val_2758_);
v___x_2803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2803_, 0, v_val_2758_);
lean_ctor_set(v___x_2803_, 1, v_fst_2768_);
lean_ctor_set(v___x_2803_, 2, v_val_2772_);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v_val_2778_);
lean_ctor_set(v___x_2804_, 2, v_fst_2788_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 2);
lean_ctor_set(v___x_2780_, 0, v___x_2804_);
v___x_2806_ = v___x_2780_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2807_ = lean_box(0);
lean_inc(v_val_2758_);
v___x_2808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2797_, v_val_2758_, v___x_2806_);
v___x_2809_ = lean_array_push(v_constOrder_2798_, v_val_2758_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 6, v___x_2809_);
lean_ctor_set(v___x_2800_, 5, v___x_2808_);
v___x_2811_ = v___x_2800_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_stream_2792_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_nameMap_2793_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_levelMap_2794_);
lean_ctor_set(v_reuseFailAlloc_2818_, 3, v_exprMap_2795_);
lean_ctor_set(v_reuseFailAlloc_2818_, 4, v_recursorRuleMap_2796_);
lean_ctor_set(v_reuseFailAlloc_2818_, 5, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2818_, 6, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 1, v___x_2811_);
lean_ctor_set(v___x_2790_, 0, v___x_2807_);
v___x_2813_ = v___x_2790_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2813_);
v___x_2815_ = v___x_2785_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_del_object(v___x_2800_);
lean_dec_ref(v_constOrder_2798_);
lean_dec_ref(v_constMap_2797_);
lean_dec_ref(v_recursorRuleMap_2796_);
lean_dec_ref(v_exprMap_2795_);
lean_dec_ref(v_levelMap_2794_);
lean_dec_ref(v_nameMap_2793_);
lean_dec_ref(v_stream_2792_);
lean_del_object(v___x_2790_);
lean_dec(v_fst_2788_);
lean_dec(v_val_2778_);
lean_dec(v_val_2772_);
lean_dec(v_fst_2768_);
v___x_2820_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_2821_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2758_, v___x_2802_);
v___x_2822_ = lean_string_append(v___x_2820_, v___x_2821_);
lean_dec_ref(v___x_2821_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 18);
lean_ctor_set(v___x_2780_, 0, v___x_2822_);
v___x_2824_ = v___x_2780_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 1);
lean_ctor_set(v___x_2785_, 0, v___x_2824_);
v___x_2826_ = v___x_2785_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_del_object(v___x_2780_);
lean_dec(v_val_2778_);
lean_dec(v_val_2772_);
lean_dec(v_fst_2768_);
lean_dec(v_val_2758_);
v_a_2832_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2782_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2782_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
lean_dec(v___x_2777_);
lean_dec(v_val_2772_);
lean_dec(v_fst_2768_);
lean_dec(v_snd_2767_);
lean_dec(v_val_2758_);
lean_dec_ref(v_elems_2751_);
v___x_2841_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2842_ = l_Nat_reprFast(v_a_2776_);
v___x_2843_ = lean_string_append(v___x_2841_, v___x_2842_);
lean_dec_ref(v___x_2842_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 18);
lean_ctor_set(v___x_2774_, 0, v___x_2843_);
v___x_2845_ = v___x_2774_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 1);
lean_ctor_set(v___x_2765_, 0, v___x_2845_);
v___x_2847_ = v___x_2765_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec(v___x_2771_);
lean_dec(v_fst_2768_);
lean_dec(v_snd_2767_);
lean_dec(v_val_2758_);
lean_dec_ref(v_elems_2751_);
lean_dec(v_mantissa_2741_);
v___x_2851_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_2852_ = l_Nat_reprFast(v_a_2770_);
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
lean_dec_ref(v___x_2852_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 18);
lean_ctor_set(v___x_2760_, 0, v___x_2853_);
v___x_2855_ = v___x_2760_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 1);
lean_ctor_set(v___x_2765_, 0, v___x_2855_);
v___x_2857_ = v___x_2765_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_del_object(v___x_2760_);
lean_dec(v_val_2758_);
lean_dec_ref(v_elems_2751_);
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
v_a_2861_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2762_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2762_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_dec(v___x_2757_);
lean_dec_ref(v_elems_2751_);
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec_ref(v_a_2698_);
v___x_2870_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_2871_ = l_Nat_reprFast(v_a_2756_);
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
lean_dec_ref(v___x_2871_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 18);
lean_ctor_set(v___x_2753_, 0, v___x_2872_);
v___x_2874_ = v___x_2753_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2874_);
v___x_2876_ = v___x_2749_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
else
{
lean_del_object(v___x_2749_);
lean_dec(v_val_2747_);
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2712_;
}
}
}
else
{
lean_dec(v___x_2746_);
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2712_;
}
}
}
else
{
lean_dec(v_exponent_2742_);
lean_dec(v_mantissa_2741_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2709_;
}
}
else
{
lean_dec(v_val_2739_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2709_;
}
}
else
{
lean_dec(v___x_2738_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2709_;
}
}
}
else
{
lean_dec(v_exponent_2734_);
lean_dec(v_mantissa_2733_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2706_;
}
}
else
{
lean_dec(v_val_2731_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2706_;
}
}
else
{
lean_dec(v___x_2730_);
lean_dec_ref(v_elems_2728_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2706_;
}
}
else
{
lean_dec(v_val_2727_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2703_;
}
}
else
{
lean_dec(v___x_2726_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2703_;
}
}
}
else
{
lean_dec(v_exponent_2720_);
lean_dec(v_mantissa_2719_);
lean_dec_ref(v_a_2698_);
goto v___jp_2700_;
}
}
else
{
lean_dec(v_val_2717_);
lean_dec_ref(v_a_2698_);
goto v___jp_2700_;
}
}
else
{
lean_dec(v___x_2716_);
lean_dec_ref(v_a_2698_);
goto v___jp_2700_;
}
v___jp_2700_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
v___jp_2703_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
v___jp_2706_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
v___jp_2709_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
v___jp_2712_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___closed__1));
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo___boxed(lean_object* v_data_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_data_2881_, v_a_2882_);
lean_dec(v_data_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(lean_object* v_data_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_2907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_2906_);
if (lean_obj_tag(v___x_2907_) == 1)
{
lean_object* v_val_2908_; 
v_val_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v___x_2907_, 1);
if (lean_obj_tag(v_val_2908_) == 2)
{
lean_object* v_n_2909_; lean_object* v_mantissa_2910_; lean_object* v_exponent_2911_; lean_object* v_natZero_2912_; lean_object* v_intZero_2913_; uint8_t v_isNeg_2914_; 
v_n_2909_ = lean_ctor_get(v_val_2908_, 0);
lean_inc_ref(v_n_2909_);
lean_dec_ref_known(v_val_2908_, 1);
v_mantissa_2910_ = lean_ctor_get(v_n_2909_, 0);
lean_inc(v_mantissa_2910_);
v_exponent_2911_ = lean_ctor_get(v_n_2909_, 1);
lean_inc(v_exponent_2911_);
lean_dec_ref(v_n_2909_);
v_natZero_2912_ = lean_unsigned_to_nat(0u);
v_intZero_2913_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_2914_ = lean_int_dec_lt(v_mantissa_2910_, v_intZero_2913_);
if (v_isNeg_2914_ == 0)
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_nat_dec_eq(v_exponent_2911_, v_natZero_2912_);
lean_dec(v_exponent_2911_);
if (v___x_2915_ == 0)
{
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2903_;
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_2917_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_2916_);
if (lean_obj_tag(v___x_2917_) == 1)
{
lean_object* v_val_2918_; 
v_val_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v___x_2917_, 1);
if (lean_obj_tag(v_val_2918_) == 4)
{
lean_object* v_elems_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_elems_2919_ = lean_ctor_get(v_val_2918_, 0);
lean_inc_ref(v_elems_2919_);
lean_dec_ref_known(v_val_2918_, 1);
v___x_2920_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_2921_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_2920_);
if (lean_obj_tag(v___x_2921_) == 1)
{
lean_object* v_val_2922_; 
v_val_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v___x_2921_, 1);
if (lean_obj_tag(v_val_2922_) == 2)
{
lean_object* v_n_2923_; lean_object* v_mantissa_2924_; lean_object* v_exponent_2925_; uint8_t v_isNeg_2926_; 
v_n_2923_ = lean_ctor_get(v_val_2922_, 0);
lean_inc_ref(v_n_2923_);
lean_dec_ref_known(v_val_2922_, 1);
v_mantissa_2924_ = lean_ctor_get(v_n_2923_, 0);
lean_inc(v_mantissa_2924_);
v_exponent_2925_ = lean_ctor_get(v_n_2923_, 1);
lean_inc(v_exponent_2925_);
lean_dec_ref(v_n_2923_);
v_isNeg_2926_ = lean_int_dec_lt(v_mantissa_2924_, v_intZero_2913_);
if (v_isNeg_2926_ == 0)
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_eq(v_exponent_2925_, v_natZero_2912_);
lean_dec(v_exponent_2925_);
if (v___x_2927_ == 0)
{
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2897_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE___closed__2));
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_2928_);
if (lean_obj_tag(v___x_2929_) == 1)
{
lean_object* v_val_2930_; 
v_val_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v___x_2929_, 1);
if (lean_obj_tag(v_val_2930_) == 2)
{
lean_object* v_n_2931_; lean_object* v_mantissa_2932_; lean_object* v_exponent_2933_; uint8_t v_isNeg_2934_; 
v_n_2931_ = lean_ctor_get(v_val_2930_, 0);
lean_inc_ref(v_n_2931_);
lean_dec_ref_known(v_val_2930_, 1);
v_mantissa_2932_ = lean_ctor_get(v_n_2931_, 0);
lean_inc(v_mantissa_2932_);
v_exponent_2933_ = lean_ctor_get(v_n_2931_, 1);
lean_inc(v_exponent_2933_);
lean_dec_ref(v_n_2931_);
v_isNeg_2934_ = lean_int_dec_lt(v_mantissa_2932_, v_intZero_2913_);
if (v_isNeg_2934_ == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_nat_dec_eq(v_exponent_2933_, v_natZero_2912_);
lean_dec(v_exponent_2933_);
if (v___x_2935_ == 0)
{
lean_dec(v_mantissa_2932_);
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2894_;
}
else
{
lean_object* v_a_2936_; lean_object* v_a_2937_; lean_object* v_a_2938_; uint8_t v_b_2940_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_a_2936_ = lean_nat_abs(v_mantissa_2910_);
lean_dec(v_mantissa_2910_);
v_a_2937_ = lean_nat_abs(v_mantissa_2924_);
lean_dec(v_mantissa_2924_);
v_a_2938_ = lean_nat_abs(v_mantissa_2932_);
lean_dec(v_mantissa_2932_);
v___x_3074_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3075_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_3074_);
if (lean_obj_tag(v___x_3075_) == 0)
{
v_b_2940_ = v_isNeg_2934_;
goto v___jp_2939_;
}
else
{
lean_object* v_val_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3085_; 
v_val_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_val_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
if (lean_obj_tag(v_val_3076_) == 1)
{
uint8_t v_b_3080_; 
lean_del_object(v___x_3078_);
v_b_3080_ = lean_ctor_get_uint8(v_val_3076_, 0);
lean_dec_ref_known(v_val_3076_, 0);
v_b_2940_ = v_b_3080_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
lean_dec(v_val_3076_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_elems_2919_);
lean_dec_ref(v_a_2889_);
v___x_3081_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__1));
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3081_);
v___x_3083_ = v___x_3078_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
v___jp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_2942_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_2888_, v___x_2941_);
if (lean_obj_tag(v___x_2942_) == 1)
{
lean_object* v_val_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3073_; 
v_val_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_3073_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_val_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3073_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
if (lean_obj_tag(v_val_2943_) == 4)
{
lean_object* v_elems_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3072_; 
v_elems_2947_ = lean_ctor_get(v_val_2943_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_val_2943_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_2949_ = v_val_2943_;
v_isShared_2950_ = v_isSharedCheck_3072_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_elems_2947_);
lean_dec(v_val_2943_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3072_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_nameMap_2951_; lean_object* v___x_2952_; 
v_nameMap_2951_ = lean_ctor_get(v_a_2889_, 1);
v___x_2952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_2951_, v_a_2936_);
if (lean_obj_tag(v___x_2952_) == 1)
{
lean_object* v_val_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_2949_);
lean_del_object(v___x_2945_);
lean_dec(v_a_2936_);
v_val_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3062_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_val_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3062_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; 
v___x_2957_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2919_, v_a_2889_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_3053_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_3053_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_3053_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_snd_2962_; lean_object* v_fst_2963_; lean_object* v_exprMap_2964_; lean_object* v___x_2965_; 
v_snd_2962_ = lean_ctor_get(v_a_2958_, 1);
lean_inc(v_snd_2962_);
v_fst_2963_ = lean_ctor_get(v_a_2958_, 0);
lean_inc(v_fst_2963_);
lean_dec(v_a_2958_);
v_exprMap_2964_ = lean_ctor_get(v_snd_2962_, 3);
v___x_2965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2964_, v_a_2937_);
if (lean_obj_tag(v___x_2965_) == 1)
{
lean_object* v_val_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_2955_);
lean_dec(v_a_2937_);
v_val_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_3043_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_val_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3043_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_2964_, v_a_2938_);
if (lean_obj_tag(v___x_2970_) == 1)
{
lean_object* v_val_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_2968_);
lean_del_object(v___x_2960_);
lean_dec(v_a_2938_);
v_val_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_3033_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_val_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3033_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_2947_, v_snd_2962_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3024_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3024_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3024_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_snd_2980_; lean_object* v_fst_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3023_; 
v_snd_2980_ = lean_ctor_get(v_a_2976_, 1);
v_fst_2981_ = lean_ctor_get(v_a_2976_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2983_ = v_a_2976_;
v_isShared_2984_ = v_isSharedCheck_3023_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2981_);
lean_dec(v_a_2976_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3023_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_stream_2985_; lean_object* v_nameMap_2986_; lean_object* v_levelMap_2987_; lean_object* v_exprMap_2988_; lean_object* v_recursorRuleMap_2989_; lean_object* v_constMap_2990_; lean_object* v_constOrder_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3022_; 
v_stream_2985_ = lean_ctor_get(v_snd_2980_, 0);
v_nameMap_2986_ = lean_ctor_get(v_snd_2980_, 1);
v_levelMap_2987_ = lean_ctor_get(v_snd_2980_, 2);
v_exprMap_2988_ = lean_ctor_get(v_snd_2980_, 3);
v_recursorRuleMap_2989_ = lean_ctor_get(v_snd_2980_, 4);
v_constMap_2990_ = lean_ctor_get(v_snd_2980_, 5);
v_constOrder_2991_ = lean_ctor_get(v_snd_2980_, 6);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_snd_2980_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2993_ = v_snd_2980_;
v_isShared_2994_ = v_isSharedCheck_3022_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_constOrder_2991_);
lean_inc(v_constMap_2990_);
lean_inc(v_recursorRuleMap_2989_);
lean_inc(v_exprMap_2988_);
lean_inc(v_levelMap_2987_);
lean_inc(v_nameMap_2986_);
lean_inc(v_stream_2985_);
lean_dec(v_snd_2980_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3022_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint8_t v___x_2995_; 
v___x_2995_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_2990_, v_val_2953_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
lean_inc(v_val_2953_);
v___x_2996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2996_, 0, v_val_2953_);
lean_ctor_set(v___x_2996_, 1, v_fst_2963_);
lean_ctor_set(v___x_2996_, 2, v_val_2966_);
v___x_2997_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v_val_2971_);
lean_ctor_set(v___x_2997_, 2, v_fst_2981_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*3, v_b_2940_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 3);
lean_ctor_set(v___x_2973_, 0, v___x_2997_);
v___x_2999_ = v___x_2973_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3000_ = lean_box(0);
lean_inc(v_val_2953_);
v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_2990_, v_val_2953_, v___x_2999_);
v___x_3002_ = lean_array_push(v_constOrder_2991_, v_val_2953_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 6, v___x_3002_);
lean_ctor_set(v___x_2993_, 5, v___x_3001_);
v___x_3004_ = v___x_2993_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_stream_2985_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_nameMap_2986_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_levelMap_2987_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_exprMap_2988_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_recursorRuleMap_2989_);
lean_ctor_set(v_reuseFailAlloc_3011_, 5, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3011_, 6, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3006_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_3004_);
lean_ctor_set(v___x_2983_, 0, v___x_3000_);
v___x_3006_ = v___x_2983_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_3006_);
v___x_3008_ = v___x_2978_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
lean_del_object(v___x_2993_);
lean_dec_ref(v_constOrder_2991_);
lean_dec_ref(v_constMap_2990_);
lean_dec_ref(v_recursorRuleMap_2989_);
lean_dec_ref(v_exprMap_2988_);
lean_dec_ref(v_levelMap_2987_);
lean_dec_ref(v_nameMap_2986_);
lean_dec_ref(v_stream_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_fst_2981_);
lean_dec(v_val_2971_);
lean_dec(v_val_2966_);
lean_dec(v_fst_2963_);
v___x_3013_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_2953_, v___x_2995_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 18);
lean_ctor_set(v___x_2973_, 0, v___x_3015_);
v___x_3017_ = v___x_2973_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 1);
lean_ctor_set(v___x_2978_, 0, v___x_3017_);
v___x_3019_ = v___x_2978_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_del_object(v___x_2973_);
lean_dec(v_val_2971_);
lean_dec(v_val_2966_);
lean_dec(v_fst_2963_);
lean_dec(v_val_2953_);
v_a_3025_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2975_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2975_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_dec(v___x_2970_);
lean_dec(v_val_2966_);
lean_dec(v_fst_2963_);
lean_dec(v_snd_2962_);
lean_dec(v_val_2953_);
lean_dec_ref(v_elems_2947_);
v___x_3034_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3035_ = l_Nat_reprFast(v_a_2938_);
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
lean_dec_ref(v___x_3035_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 18);
lean_ctor_set(v___x_2968_, 0, v___x_3036_);
v___x_3038_ = v___x_2968_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
lean_ctor_set(v___x_2960_, 0, v___x_3038_);
v___x_3040_ = v___x_2960_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
else
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_dec(v___x_2965_);
lean_dec(v_fst_2963_);
lean_dec(v_snd_2962_);
lean_dec(v_val_2953_);
lean_dec_ref(v_elems_2947_);
lean_dec(v_a_2938_);
v___x_3044_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3045_ = l_Nat_reprFast(v_a_2937_);
v___x_3046_ = lean_string_append(v___x_3044_, v___x_3045_);
lean_dec_ref(v___x_3045_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 18);
lean_ctor_set(v___x_2955_, 0, v___x_3046_);
v___x_3048_ = v___x_2955_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
lean_ctor_set(v___x_2960_, 0, v___x_3048_);
v___x_3050_ = v___x_2960_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_del_object(v___x_2955_);
lean_dec(v_val_2953_);
lean_dec_ref(v_elems_2947_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
v_a_3054_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2957_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2957_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
lean_dec(v___x_2952_);
lean_dec_ref(v_elems_2947_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_elems_2919_);
lean_dec_ref(v_a_2889_);
v___x_3063_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3064_ = l_Nat_reprFast(v_a_2936_);
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
lean_dec_ref(v___x_3064_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 18);
lean_ctor_set(v___x_2949_, 0, v___x_3065_);
v___x_3067_ = v___x_2949_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3069_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_3067_);
v___x_3069_ = v___x_2945_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
else
{
lean_del_object(v___x_2945_);
lean_dec(v_val_2943_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_elems_2919_);
lean_dec_ref(v_a_2889_);
goto v___jp_2891_;
}
}
}
else
{
lean_dec(v___x_2942_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_elems_2919_);
lean_dec_ref(v_a_2889_);
goto v___jp_2891_;
}
}
}
}
else
{
lean_dec(v_exponent_2933_);
lean_dec(v_mantissa_2932_);
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2894_;
}
}
else
{
lean_dec(v_val_2930_);
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2894_;
}
}
else
{
lean_dec(v___x_2929_);
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2894_;
}
}
}
else
{
lean_dec(v_exponent_2925_);
lean_dec(v_mantissa_2924_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2897_;
}
}
else
{
lean_dec(v_val_2922_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2897_;
}
}
else
{
lean_dec(v___x_2921_);
lean_dec_ref(v_elems_2919_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2897_;
}
}
else
{
lean_dec(v_val_2918_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2900_;
}
}
else
{
lean_dec(v___x_2917_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2900_;
}
}
}
else
{
lean_dec(v_exponent_2911_);
lean_dec(v_mantissa_2910_);
lean_dec_ref(v_a_2889_);
goto v___jp_2903_;
}
}
else
{
lean_dec(v_val_2908_);
lean_dec_ref(v_a_2889_);
goto v___jp_2903_;
}
}
else
{
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2889_);
goto v___jp_2903_;
}
v___jp_2891_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
v___jp_2894_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
v___jp_2897_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
v___jp_2900_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
v___jp_2903_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___closed__1));
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo___boxed(lean_object* v_data_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_data_3086_, v_a_3087_);
lean_dec(v_data_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(lean_object* v_data_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3114_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3098_, v___x_3113_);
if (lean_obj_tag(v___x_3114_) == 1)
{
lean_object* v_val_3115_; 
v_val_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v___x_3114_, 1);
if (lean_obj_tag(v_val_3115_) == 2)
{
lean_object* v_n_3116_; lean_object* v_mantissa_3117_; lean_object* v_exponent_3118_; lean_object* v_natZero_3119_; lean_object* v_intZero_3120_; uint8_t v_isNeg_3121_; 
v_n_3116_ = lean_ctor_get(v_val_3115_, 0);
lean_inc_ref(v_n_3116_);
lean_dec_ref_known(v_val_3115_, 1);
v_mantissa_3117_ = lean_ctor_get(v_n_3116_, 0);
lean_inc(v_mantissa_3117_);
v_exponent_3118_ = lean_ctor_get(v_n_3116_, 1);
lean_inc(v_exponent_3118_);
lean_dec_ref(v_n_3116_);
v_natZero_3119_ = lean_unsigned_to_nat(0u);
v_intZero_3120_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3121_ = lean_int_dec_lt(v_mantissa_3117_, v_intZero_3120_);
if (v_isNeg_3121_ == 0)
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_eq(v_exponent_3118_, v_natZero_3119_);
lean_dec(v_exponent_3118_);
if (v___x_3122_ == 0)
{
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3110_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3098_, v___x_3123_);
if (lean_obj_tag(v___x_3124_) == 1)
{
lean_object* v_val_3125_; 
v_val_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_val_3125_);
lean_dec_ref_known(v___x_3124_, 1);
if (lean_obj_tag(v_val_3125_) == 4)
{
lean_object* v_elems_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_elems_3126_ = lean_ctor_get(v_val_3125_, 0);
lean_inc_ref(v_elems_3126_);
lean_dec_ref_known(v_val_3125_, 1);
v___x_3127_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3098_, v___x_3127_);
if (lean_obj_tag(v___x_3128_) == 1)
{
lean_object* v_val_3129_; 
v_val_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_val_3129_);
lean_dec_ref_known(v___x_3128_, 1);
if (lean_obj_tag(v_val_3129_) == 2)
{
lean_object* v_n_3130_; lean_object* v_mantissa_3131_; lean_object* v_exponent_3132_; uint8_t v_isNeg_3133_; 
v_n_3130_ = lean_ctor_get(v_val_3129_, 0);
lean_inc_ref(v_n_3130_);
lean_dec_ref_known(v_val_3129_, 1);
v_mantissa_3131_ = lean_ctor_get(v_n_3130_, 0);
lean_inc(v_mantissa_3131_);
v_exponent_3132_ = lean_ctor_get(v_n_3130_, 1);
lean_inc(v_exponent_3132_);
lean_dec_ref(v_n_3130_);
v_isNeg_3133_ = lean_int_dec_lt(v_mantissa_3131_, v_intZero_3120_);
if (v_isNeg_3133_ == 0)
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_nat_dec_eq(v_exponent_3132_, v_natZero_3119_);
lean_dec(v_exponent_3132_);
if (v___x_3134_ == 0)
{
lean_dec(v_mantissa_3131_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3104_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__2));
v___x_3136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_3098_, v___x_3135_);
if (lean_obj_tag(v___x_3136_) == 1)
{
lean_object* v_val_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3265_; 
v_val_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3265_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_val_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3265_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
if (lean_obj_tag(v_val_3137_) == 3)
{
lean_object* v_s_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3264_; 
v_s_3141_ = lean_ctor_get(v_val_3137_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_val_3137_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3143_ = v_val_3137_;
v_isShared_3144_ = v_isSharedCheck_3264_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_s_3141_);
lean_dec(v_val_3137_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3264_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v_nameMap_3145_; lean_object* v_a_3146_; lean_object* v___x_3147_; 
v_nameMap_3145_ = lean_ctor_get(v_a_3099_, 1);
v_a_3146_ = lean_nat_abs(v_mantissa_3117_);
lean_dec(v_mantissa_3117_);
v___x_3147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3145_, v_a_3146_);
if (lean_obj_tag(v___x_3147_) == 1)
{
lean_object* v_val_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_a_3146_);
lean_del_object(v___x_3139_);
v_val_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3254_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_val_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3254_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; 
v___x_3152_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3126_, v_a_3099_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3245_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3245_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3245_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_snd_3157_; lean_object* v_fst_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3244_; 
v_snd_3157_ = lean_ctor_get(v_a_3153_, 1);
v_fst_3158_ = lean_ctor_get(v_a_3153_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_a_3153_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3160_ = v_a_3153_;
v_isShared_3161_ = v_isSharedCheck_3244_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3157_);
lean_inc(v_fst_3158_);
lean_dec(v_a_3153_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3244_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_stream_3162_; lean_object* v_nameMap_3163_; lean_object* v_levelMap_3164_; lean_object* v_exprMap_3165_; lean_object* v_recursorRuleMap_3166_; lean_object* v_constMap_3167_; lean_object* v_constOrder_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3243_; 
v_stream_3162_ = lean_ctor_get(v_snd_3157_, 0);
v_nameMap_3163_ = lean_ctor_get(v_snd_3157_, 1);
v_levelMap_3164_ = lean_ctor_get(v_snd_3157_, 2);
v_exprMap_3165_ = lean_ctor_get(v_snd_3157_, 3);
v_recursorRuleMap_3166_ = lean_ctor_get(v_snd_3157_, 4);
v_constMap_3167_ = lean_ctor_get(v_snd_3157_, 5);
v_constOrder_3168_ = lean_ctor_get(v_snd_3157_, 6);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_snd_3157_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3170_ = v_snd_3157_;
v_isShared_3171_ = v_isSharedCheck_3243_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_constOrder_3168_);
lean_inc(v_constMap_3167_);
lean_inc(v_recursorRuleMap_3166_);
lean_inc(v_exprMap_3165_);
lean_inc(v_levelMap_3164_);
lean_inc(v_nameMap_3163_);
lean_inc(v_stream_3162_);
lean_dec(v_snd_3157_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3243_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_a_3172_; lean_object* v___x_3173_; 
v_a_3172_ = lean_nat_abs(v_mantissa_3131_);
lean_dec(v_mantissa_3131_);
v___x_3173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3165_, v_a_3172_);
if (lean_obj_tag(v___x_3173_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v_a_3172_);
v_val_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3233_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_val_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3233_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
uint8_t v_kind_3179_; lean_object* v_stream_3180_; lean_object* v_nameMap_3181_; lean_object* v_levelMap_3182_; lean_object* v_exprMap_3183_; lean_object* v_recursorRuleMap_3184_; lean_object* v_constMap_3185_; lean_object* v_constOrder_3186_; uint8_t v___x_3214_; 
v___x_3214_ = lean_string_dec_eq(v_s_3141_, v___x_3127_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3216_ = lean_string_dec_eq(v_s_3141_, v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__4));
v___x_3218_ = lean_string_dec_eq(v_s_3141_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__5));
v___x_3220_ = lean_string_dec_eq(v_s_3141_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_del_object(v___x_3176_);
lean_dec(v_val_3174_);
lean_del_object(v___x_3170_);
lean_dec_ref(v_constOrder_3168_);
lean_dec_ref(v_constMap_3167_);
lean_dec_ref(v_recursorRuleMap_3166_);
lean_dec_ref(v_exprMap_3165_);
lean_dec_ref(v_levelMap_3164_);
lean_dec_ref(v_nameMap_3163_);
lean_dec_ref(v_stream_3162_);
lean_del_object(v___x_3160_);
lean_dec(v_fst_3158_);
lean_del_object(v___x_3155_);
lean_dec(v_val_3148_);
v___x_3221_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__6));
v___x_3222_ = lean_string_append(v___x_3221_, v_s_3141_);
lean_dec_ref(v_s_3141_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 18);
lean_ctor_set(v___x_3150_, 0, v___x_3222_);
v___x_3224_ = v___x_3150_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 1);
lean_ctor_set(v___x_3143_, 0, v___x_3224_);
v___x_3226_ = v___x_3143_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
else
{
uint8_t v___x_3229_; 
lean_del_object(v___x_3150_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
v___x_3229_ = 3;
v_kind_3179_ = v___x_3229_;
v_stream_3180_ = v_stream_3162_;
v_nameMap_3181_ = v_nameMap_3163_;
v_levelMap_3182_ = v_levelMap_3164_;
v_exprMap_3183_ = v_exprMap_3165_;
v_recursorRuleMap_3184_ = v_recursorRuleMap_3166_;
v_constMap_3185_ = v_constMap_3167_;
v_constOrder_3186_ = v_constOrder_3168_;
goto v___jp_3178_;
}
}
else
{
uint8_t v___x_3230_; 
lean_del_object(v___x_3150_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
v___x_3230_ = 2;
v_kind_3179_ = v___x_3230_;
v_stream_3180_ = v_stream_3162_;
v_nameMap_3181_ = v_nameMap_3163_;
v_levelMap_3182_ = v_levelMap_3164_;
v_exprMap_3183_ = v_exprMap_3165_;
v_recursorRuleMap_3184_ = v_recursorRuleMap_3166_;
v_constMap_3185_ = v_constMap_3167_;
v_constOrder_3186_ = v_constOrder_3168_;
goto v___jp_3178_;
}
}
else
{
uint8_t v___x_3231_; 
lean_del_object(v___x_3150_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
v___x_3231_ = 1;
v_kind_3179_ = v___x_3231_;
v_stream_3180_ = v_stream_3162_;
v_nameMap_3181_ = v_nameMap_3163_;
v_levelMap_3182_ = v_levelMap_3164_;
v_exprMap_3183_ = v_exprMap_3165_;
v_recursorRuleMap_3184_ = v_recursorRuleMap_3166_;
v_constMap_3185_ = v_constMap_3167_;
v_constOrder_3186_ = v_constOrder_3168_;
goto v___jp_3178_;
}
}
else
{
uint8_t v___x_3232_; 
lean_del_object(v___x_3150_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
v___x_3232_ = 0;
v_kind_3179_ = v___x_3232_;
v_stream_3180_ = v_stream_3162_;
v_nameMap_3181_ = v_nameMap_3163_;
v_levelMap_3182_ = v_levelMap_3164_;
v_exprMap_3183_ = v_exprMap_3165_;
v_recursorRuleMap_3184_ = v_recursorRuleMap_3166_;
v_constMap_3185_ = v_constMap_3167_;
v_constOrder_3186_ = v_constOrder_3168_;
goto v___jp_3178_;
}
v___jp_3178_:
{
uint8_t v___x_3187_; 
v___x_3187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3185_, v_val_3148_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_inc(v_val_3148_);
v___x_3188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3188_, 0, v_val_3148_);
lean_ctor_set(v___x_3188_, 1, v_fst_3158_);
lean_ctor_set(v___x_3188_, 2, v_val_3174_);
v___x_3189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*1, v_kind_3179_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 4);
lean_ctor_set(v___x_3176_, 0, v___x_3189_);
v___x_3191_ = v___x_3176_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3192_ = lean_box(0);
lean_inc(v_val_3148_);
v___x_3193_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3185_, v_val_3148_, v___x_3191_);
v___x_3194_ = lean_array_push(v_constOrder_3186_, v_val_3148_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 6, v___x_3194_);
lean_ctor_set(v___x_3170_, 5, v___x_3193_);
lean_ctor_set(v___x_3170_, 4, v_recursorRuleMap_3184_);
lean_ctor_set(v___x_3170_, 3, v_exprMap_3183_);
lean_ctor_set(v___x_3170_, 2, v_levelMap_3182_);
lean_ctor_set(v___x_3170_, 1, v_nameMap_3181_);
lean_ctor_set(v___x_3170_, 0, v_stream_3180_);
v___x_3196_ = v___x_3170_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_stream_3180_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_nameMap_3181_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_levelMap_3182_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_exprMap_3183_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_recursorRuleMap_3184_);
lean_ctor_set(v_reuseFailAlloc_3203_, 5, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3203_, 6, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3196_);
lean_ctor_set(v___x_3160_, 0, v___x_3192_);
v___x_3198_ = v___x_3160_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3198_);
v___x_3200_ = v___x_3155_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_dec_ref(v_constOrder_3186_);
lean_dec_ref(v_constMap_3185_);
lean_dec_ref(v_recursorRuleMap_3184_);
lean_dec_ref(v_exprMap_3183_);
lean_dec_ref(v_levelMap_3182_);
lean_dec_ref(v_nameMap_3181_);
lean_dec_ref(v_stream_3180_);
lean_dec(v_val_3174_);
lean_del_object(v___x_3170_);
lean_del_object(v___x_3160_);
lean_dec(v_fst_3158_);
v___x_3205_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3148_, v___x_3187_);
v___x_3207_ = lean_string_append(v___x_3205_, v___x_3206_);
lean_dec_ref(v___x_3206_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 18);
lean_ctor_set(v___x_3176_, 0, v___x_3207_);
v___x_3209_ = v___x_3176_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3211_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
lean_ctor_set(v___x_3155_, 0, v___x_3209_);
v___x_3211_ = v___x_3155_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_dec(v___x_3173_);
lean_del_object(v___x_3170_);
lean_dec_ref(v_constOrder_3168_);
lean_dec_ref(v_constMap_3167_);
lean_dec_ref(v_recursorRuleMap_3166_);
lean_dec_ref(v_exprMap_3165_);
lean_dec_ref(v_levelMap_3164_);
lean_dec_ref(v_nameMap_3163_);
lean_dec_ref(v_stream_3162_);
lean_del_object(v___x_3160_);
lean_dec(v_fst_3158_);
lean_dec(v_val_3148_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
v___x_3234_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3235_ = l_Nat_reprFast(v_a_3172_);
v___x_3236_ = lean_string_append(v___x_3234_, v___x_3235_);
lean_dec_ref(v___x_3235_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 18);
lean_ctor_set(v___x_3150_, 0, v___x_3236_);
v___x_3238_ = v___x_3150_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
lean_ctor_set(v___x_3155_, 0, v___x_3238_);
v___x_3240_ = v___x_3155_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_del_object(v___x_3150_);
lean_dec(v_val_3148_);
lean_del_object(v___x_3143_);
lean_dec_ref(v_s_3141_);
lean_dec(v_mantissa_3131_);
v_a_3246_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3152_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3152_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
lean_dec(v___x_3147_);
lean_dec_ref(v_s_3141_);
lean_dec(v_mantissa_3131_);
lean_dec_ref(v_elems_3126_);
lean_dec_ref(v_a_3099_);
v___x_3255_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3256_ = l_Nat_reprFast(v_a_3146_);
v___x_3257_ = lean_string_append(v___x_3255_, v___x_3256_);
lean_dec_ref(v___x_3256_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 18);
lean_ctor_set(v___x_3143_, 0, v___x_3257_);
v___x_3259_ = v___x_3143_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3261_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3259_);
v___x_3261_ = v___x_3139_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_del_object(v___x_3139_);
lean_dec(v_val_3137_);
lean_dec(v_mantissa_3131_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3101_;
}
}
}
else
{
lean_dec(v___x_3136_);
lean_dec(v_mantissa_3131_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3101_;
}
}
}
else
{
lean_dec(v_exponent_3132_);
lean_dec(v_mantissa_3131_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3104_;
}
}
else
{
lean_dec(v_val_3129_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3104_;
}
}
else
{
lean_dec(v___x_3128_);
lean_dec_ref(v_elems_3126_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3104_;
}
}
else
{
lean_dec(v_val_3125_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3107_;
}
}
else
{
lean_dec(v___x_3124_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3107_;
}
}
}
else
{
lean_dec(v_exponent_3118_);
lean_dec(v_mantissa_3117_);
lean_dec_ref(v_a_3099_);
goto v___jp_3110_;
}
}
else
{
lean_dec(v_val_3115_);
lean_dec_ref(v_a_3099_);
goto v___jp_3110_;
}
}
else
{
lean_dec(v___x_3114_);
lean_dec_ref(v_a_3099_);
goto v___jp_3110_;
}
v___jp_3101_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
v___jp_3104_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
v___jp_3107_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
v___jp_3110_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__1));
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___boxed(lean_object* v_data_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_data_3266_, v_a_3267_);
lean_dec(v_data_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(lean_object* v_json_3282_, lean_object* v_a_3283_){
_start:
{
if (lean_obj_tag(v_json_3282_) == 5)
{
lean_object* v_kvPairs_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_kvPairs_3318_ = lean_ctor_get(v_json_3282_, 0);
v___x_3319_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 1)
{
lean_object* v_val_3321_; 
v_val_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v___x_3320_, 1);
if (lean_obj_tag(v_val_3321_) == 2)
{
lean_object* v_n_3322_; lean_object* v_mantissa_3323_; lean_object* v_exponent_3324_; lean_object* v_natZero_3325_; lean_object* v_intZero_3326_; uint8_t v_isNeg_3327_; 
v_n_3322_ = lean_ctor_get(v_val_3321_, 0);
lean_inc_ref(v_n_3322_);
lean_dec_ref_known(v_val_3321_, 1);
v_mantissa_3323_ = lean_ctor_get(v_n_3322_, 0);
lean_inc(v_mantissa_3323_);
v_exponent_3324_ = lean_ctor_get(v_n_3322_, 1);
lean_inc(v_exponent_3324_);
lean_dec_ref(v_n_3322_);
v_natZero_3325_ = lean_unsigned_to_nat(0u);
v_intZero_3326_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3327_ = lean_int_dec_lt(v_mantissa_3323_, v_intZero_3326_);
if (v_isNeg_3327_ == 0)
{
uint8_t v___x_3328_; 
v___x_3328_ = lean_nat_dec_eq(v_exponent_3324_, v_natZero_3325_);
lean_dec(v_exponent_3324_);
if (v___x_3328_ == 0)
{
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3285_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3329_);
if (lean_obj_tag(v___x_3330_) == 1)
{
lean_object* v_val_3331_; 
v_val_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3330_, 1);
if (lean_obj_tag(v_val_3331_) == 4)
{
lean_object* v_elems_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_elems_3332_ = lean_ctor_get(v_val_3331_, 0);
lean_inc_ref(v_elems_3332_);
lean_dec_ref_known(v_val_3331_, 1);
v___x_3333_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 1)
{
lean_object* v_val_3335_; 
v_val_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v___x_3334_, 1);
if (lean_obj_tag(v_val_3335_) == 2)
{
lean_object* v_n_3336_; lean_object* v_mantissa_3337_; lean_object* v_exponent_3338_; uint8_t v_isNeg_3339_; 
v_n_3336_ = lean_ctor_get(v_val_3335_, 0);
lean_inc_ref(v_n_3336_);
lean_dec_ref_known(v_val_3335_, 1);
v_mantissa_3337_ = lean_ctor_get(v_n_3336_, 0);
lean_inc(v_mantissa_3337_);
v_exponent_3338_ = lean_ctor_get(v_n_3336_, 1);
lean_inc(v_exponent_3338_);
lean_dec_ref(v_n_3336_);
v_isNeg_3339_ = lean_int_dec_lt(v_mantissa_3337_, v_intZero_3326_);
if (v_isNeg_3339_ == 0)
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_nat_dec_eq(v_exponent_3338_, v_natZero_3325_);
lean_dec(v_exponent_3338_);
if (v___x_3340_ == 0)
{
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3291_;
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3341_);
if (lean_obj_tag(v___x_3342_) == 1)
{
lean_object* v_val_3343_; 
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3342_, 1);
if (lean_obj_tag(v_val_3343_) == 2)
{
lean_object* v_n_3344_; lean_object* v_mantissa_3345_; lean_object* v_exponent_3346_; uint8_t v_isNeg_3347_; 
v_n_3344_ = lean_ctor_get(v_val_3343_, 0);
lean_inc_ref(v_n_3344_);
lean_dec_ref_known(v_val_3343_, 1);
v_mantissa_3345_ = lean_ctor_get(v_n_3344_, 0);
lean_inc(v_mantissa_3345_);
v_exponent_3346_ = lean_ctor_get(v_n_3344_, 1);
lean_inc(v_exponent_3346_);
lean_dec_ref(v_n_3344_);
v_isNeg_3347_ = lean_int_dec_lt(v_mantissa_3345_, v_intZero_3326_);
if (v_isNeg_3347_ == 0)
{
uint8_t v___x_3348_; 
v___x_3348_ = lean_nat_dec_eq(v_exponent_3346_, v_natZero_3325_);
lean_dec(v_exponent_3346_);
if (v___x_3348_ == 0)
{
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3294_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3350_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3349_);
if (lean_obj_tag(v___x_3350_) == 1)
{
lean_object* v_val_3351_; 
v_val_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___x_3350_, 1);
if (lean_obj_tag(v_val_3351_) == 2)
{
lean_object* v_n_3352_; lean_object* v_mantissa_3353_; lean_object* v_exponent_3354_; uint8_t v_isNeg_3355_; 
v_n_3352_ = lean_ctor_get(v_val_3351_, 0);
lean_inc_ref(v_n_3352_);
lean_dec_ref_known(v_val_3351_, 1);
v_mantissa_3353_ = lean_ctor_get(v_n_3352_, 0);
lean_inc(v_mantissa_3353_);
v_exponent_3354_ = lean_ctor_get(v_n_3352_, 1);
lean_inc(v_exponent_3354_);
lean_dec_ref(v_n_3352_);
v_isNeg_3355_ = lean_int_dec_lt(v_mantissa_3353_, v_intZero_3326_);
if (v_isNeg_3355_ == 0)
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_eq(v_exponent_3354_, v_natZero_3325_);
lean_dec(v_exponent_3354_);
if (v___x_3356_ == 0)
{
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3297_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3357_);
if (lean_obj_tag(v___x_3358_) == 1)
{
lean_object* v_val_3359_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3358_, 1);
if (lean_obj_tag(v_val_3359_) == 4)
{
lean_object* v_elems_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_elems_3360_ = lean_ctor_get(v_val_3359_, 0);
lean_inc_ref(v_elems_3360_);
lean_dec_ref_known(v_val_3359_, 1);
v___x_3361_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3361_);
if (lean_obj_tag(v___x_3362_) == 1)
{
lean_object* v_val_3363_; 
v_val_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_val_3363_);
lean_dec_ref_known(v___x_3362_, 1);
if (lean_obj_tag(v_val_3363_) == 4)
{
lean_object* v_elems_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_elems_3364_ = lean_ctor_get(v_val_3363_, 0);
lean_inc_ref(v_elems_3364_);
lean_dec_ref_known(v_val_3363_, 1);
v___x_3365_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__5));
v___x_3366_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3365_);
if (lean_obj_tag(v___x_3366_) == 1)
{
lean_object* v_val_3367_; 
v_val_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3366_, 1);
if (lean_obj_tag(v_val_3367_) == 2)
{
lean_object* v_n_3368_; lean_object* v_mantissa_3369_; lean_object* v_exponent_3370_; uint8_t v_isNeg_3371_; 
v_n_3368_ = lean_ctor_get(v_val_3367_, 0);
lean_inc_ref(v_n_3368_);
lean_dec_ref_known(v_val_3367_, 1);
v_mantissa_3369_ = lean_ctor_get(v_n_3368_, 0);
lean_inc(v_mantissa_3369_);
v_exponent_3370_ = lean_ctor_get(v_n_3368_, 1);
lean_inc(v_exponent_3370_);
lean_dec_ref(v_n_3368_);
v_isNeg_3371_ = lean_int_dec_lt(v_mantissa_3369_, v_intZero_3326_);
if (v_isNeg_3371_ == 0)
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_nat_dec_eq(v_exponent_3370_, v_natZero_3325_);
lean_dec(v_exponent_3370_);
if (v___x_3372_ == 0)
{
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3306_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__6));
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_val_3375_) == 1)
{
uint8_t v_b_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_b_3376_ = lean_ctor_get_uint8(v_val_3375_, 0);
lean_dec_ref_known(v_val_3375_, 0);
v___x_3377_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3377_);
if (lean_obj_tag(v___x_3378_) == 1)
{
lean_object* v_val_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3515_; 
v_val_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3515_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_val_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3515_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
if (lean_obj_tag(v_val_3379_) == 1)
{
uint8_t v_b_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_b_3383_ = lean_ctor_get_uint8(v_val_3379_, 0);
lean_dec_ref_known(v_val_3379_, 0);
v___x_3384_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__7));
v___x_3385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3318_, v___x_3384_);
if (lean_obj_tag(v___x_3385_) == 1)
{
lean_object* v_val_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3514_; 
v_val_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3514_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_val_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3514_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
if (lean_obj_tag(v_val_3386_) == 1)
{
uint8_t v_b_3390_; lean_object* v_nameMap_3391_; lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_b_3390_ = lean_ctor_get_uint8(v_val_3386_, 0);
lean_dec_ref_known(v_val_3386_, 0);
v_nameMap_3391_ = lean_ctor_get(v_a_3283_, 1);
v_a_3392_ = lean_nat_abs(v_mantissa_3323_);
lean_dec(v_mantissa_3323_);
v___x_3393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3393_) == 1)
{
lean_object* v_val_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_a_3392_);
lean_del_object(v___x_3388_);
lean_del_object(v___x_3381_);
v_val_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3504_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_val_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3504_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; 
v___x_3398_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3332_, v_a_3283_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3495_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3495_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3495_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_snd_3403_; lean_object* v_fst_3404_; lean_object* v_exprMap_3405_; lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_snd_3403_ = lean_ctor_get(v_a_3399_, 1);
lean_inc(v_snd_3403_);
v_fst_3404_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_fst_3404_);
lean_dec(v_a_3399_);
v_exprMap_3405_ = lean_ctor_get(v_snd_3403_, 3);
v_a_3406_ = lean_nat_abs(v_mantissa_3337_);
lean_dec(v_mantissa_3337_);
v___x_3407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3405_, v_a_3406_);
if (lean_obj_tag(v___x_3407_) == 1)
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3396_);
v_val_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3485_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3485_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; 
v___x_3412_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3360_, v_snd_3403_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___x_3416_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v_fst_3414_ = lean_ctor_get(v_a_3413_, 0);
lean_inc(v_fst_3414_);
v_snd_3415_ = lean_ctor_get(v_a_3413_, 1);
lean_inc(v_snd_3415_);
lean_dec(v_a_3413_);
v___x_3416_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3364_, v_snd_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3468_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3468_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3468_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_snd_3421_; lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3467_; 
v_snd_3421_ = lean_ctor_get(v_a_3417_, 1);
v_fst_3422_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3424_ = v_a_3417_;
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3422_);
lean_dec(v_a_3417_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_stream_3426_; lean_object* v_nameMap_3427_; lean_object* v_levelMap_3428_; lean_object* v_exprMap_3429_; lean_object* v_recursorRuleMap_3430_; lean_object* v_constMap_3431_; lean_object* v_constOrder_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3466_; 
v_stream_3426_ = lean_ctor_get(v_snd_3421_, 0);
v_nameMap_3427_ = lean_ctor_get(v_snd_3421_, 1);
v_levelMap_3428_ = lean_ctor_get(v_snd_3421_, 2);
v_exprMap_3429_ = lean_ctor_get(v_snd_3421_, 3);
v_recursorRuleMap_3430_ = lean_ctor_get(v_snd_3421_, 4);
v_constMap_3431_ = lean_ctor_get(v_snd_3421_, 5);
v_constOrder_3432_ = lean_ctor_get(v_snd_3421_, 6);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3434_ = v_snd_3421_;
v_isShared_3435_ = v_isSharedCheck_3466_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_constOrder_3432_);
lean_inc(v_constMap_3431_);
lean_inc(v_recursorRuleMap_3430_);
lean_inc(v_exprMap_3429_);
lean_inc(v_levelMap_3428_);
lean_inc(v_nameMap_3427_);
lean_inc(v_stream_3426_);
lean_dec(v_snd_3421_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3466_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3431_, v_val_3394_);
if (v___x_3436_ == 0)
{
lean_object* v_a_3437_; lean_object* v_a_3438_; lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v_a_3437_ = lean_nat_abs(v_mantissa_3345_);
lean_dec(v_mantissa_3345_);
v_a_3438_ = lean_nat_abs(v_mantissa_3353_);
lean_dec(v_mantissa_3353_);
v_a_3439_ = lean_nat_abs(v_mantissa_3369_);
lean_dec(v_mantissa_3369_);
lean_inc(v_val_3394_);
v___x_3440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3440_, 0, v_val_3394_);
lean_ctor_set(v___x_3440_, 1, v_fst_3404_);
lean_ctor_set(v___x_3440_, 2, v_val_3408_);
v___x_3441_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v_a_3437_);
lean_ctor_set(v___x_3441_, 2, v_a_3438_);
lean_ctor_set(v___x_3441_, 3, v_fst_3414_);
lean_ctor_set(v___x_3441_, 4, v_fst_3422_);
lean_ctor_set(v___x_3441_, 5, v_a_3439_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*6, v_b_3376_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*6 + 1, v_b_3383_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*6 + 2, v_b_3390_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 5);
lean_ctor_set(v___x_3410_, 0, v___x_3441_);
v___x_3443_ = v___x_3410_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3444_ = lean_box(0);
lean_inc(v_val_3394_);
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3431_, v_val_3394_, v___x_3443_);
v___x_3446_ = lean_array_push(v_constOrder_3432_, v_val_3394_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 6, v___x_3446_);
lean_ctor_set(v___x_3434_, 5, v___x_3445_);
v___x_3448_ = v___x_3434_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_stream_3426_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_nameMap_3427_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_levelMap_3428_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_exprMap_3429_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_recursorRuleMap_3430_);
lean_ctor_set(v_reuseFailAlloc_3455_, 5, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3455_, 6, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3448_);
lean_ctor_set(v___x_3424_, 0, v___x_3444_);
v___x_3450_ = v___x_3424_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3450_);
v___x_3452_ = v___x_3419_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_del_object(v___x_3434_);
lean_dec_ref(v_constOrder_3432_);
lean_dec_ref(v_constMap_3431_);
lean_dec_ref(v_recursorRuleMap_3430_);
lean_dec_ref(v_exprMap_3429_);
lean_dec_ref(v_levelMap_3428_);
lean_dec_ref(v_nameMap_3427_);
lean_dec_ref(v_stream_3426_);
lean_del_object(v___x_3424_);
lean_dec(v_fst_3422_);
lean_dec(v_fst_3414_);
lean_dec(v_val_3408_);
lean_dec(v_fst_3404_);
lean_dec(v_mantissa_3369_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
v___x_3457_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3394_, v___x_3436_);
v___x_3459_ = lean_string_append(v___x_3457_, v___x_3458_);
lean_dec_ref(v___x_3458_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 18);
lean_ctor_set(v___x_3410_, 0, v___x_3459_);
v___x_3461_ = v___x_3410_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 1);
lean_ctor_set(v___x_3419_, 0, v___x_3461_);
v___x_3463_ = v___x_3419_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_fst_3414_);
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec(v_fst_3404_);
lean_dec(v_val_3394_);
lean_dec(v_mantissa_3369_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
v_a_3469_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3416_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3416_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec(v_fst_3404_);
lean_dec(v_val_3394_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
v_a_3477_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3412_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3412_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec(v___x_3407_);
lean_dec(v_fst_3404_);
lean_dec(v_snd_3403_);
lean_dec(v_val_3394_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
v___x_3486_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3487_ = l_Nat_reprFast(v_a_3406_);
v___x_3488_ = lean_string_append(v___x_3486_, v___x_3487_);
lean_dec_ref(v___x_3487_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 18);
lean_ctor_set(v___x_3396_, 0, v___x_3488_);
v___x_3490_ = v___x_3396_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3490_);
v___x_3492_ = v___x_3401_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_del_object(v___x_3396_);
lean_dec(v_val_3394_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
v_a_3496_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3398_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3398_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3509_; 
lean_dec(v___x_3393_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec_ref(v_a_3283_);
v___x_3505_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3506_ = l_Nat_reprFast(v_a_3392_);
v___x_3507_ = lean_string_append(v___x_3505_, v___x_3506_);
lean_dec_ref(v___x_3506_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 18);
lean_ctor_set(v___x_3388_, 0, v___x_3507_);
v___x_3509_ = v___x_3388_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
lean_object* v___x_3511_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3509_);
v___x_3511_ = v___x_3381_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_del_object(v___x_3388_);
lean_dec(v_val_3386_);
lean_del_object(v___x_3381_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3315_;
}
}
}
else
{
lean_dec(v___x_3385_);
lean_del_object(v___x_3381_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3315_;
}
}
else
{
lean_del_object(v___x_3381_);
lean_dec(v_val_3379_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3312_;
}
}
}
else
{
lean_dec(v___x_3378_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3312_;
}
}
else
{
lean_dec(v_val_3375_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3309_;
}
}
else
{
lean_dec(v___x_3374_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3309_;
}
}
}
else
{
lean_dec(v_exponent_3370_);
lean_dec(v_mantissa_3369_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3306_;
}
}
else
{
lean_dec(v_val_3367_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3306_;
}
}
else
{
lean_dec(v___x_3366_);
lean_dec_ref(v_elems_3364_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3306_;
}
}
else
{
lean_dec(v_val_3363_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3303_;
}
}
else
{
lean_dec(v___x_3362_);
lean_dec_ref(v_elems_3360_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3303_;
}
}
else
{
lean_dec(v_val_3359_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3300_;
}
}
else
{
lean_dec(v___x_3358_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3300_;
}
}
}
else
{
lean_dec(v_exponent_3354_);
lean_dec(v_mantissa_3353_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3297_;
}
}
else
{
lean_dec(v_val_3351_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3297_;
}
}
else
{
lean_dec(v___x_3350_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3297_;
}
}
}
else
{
lean_dec(v_exponent_3346_);
lean_dec(v_mantissa_3345_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3294_;
}
}
else
{
lean_dec(v_val_3343_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3294_;
}
}
else
{
lean_dec(v___x_3342_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3294_;
}
}
}
else
{
lean_dec(v_exponent_3338_);
lean_dec(v_mantissa_3337_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3291_;
}
}
else
{
lean_dec(v_val_3335_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3291_;
}
}
else
{
lean_dec(v___x_3334_);
lean_dec_ref(v_elems_3332_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3291_;
}
}
else
{
lean_dec(v_val_3331_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3288_;
}
}
else
{
lean_dec(v___x_3330_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3288_;
}
}
}
else
{
lean_dec(v_exponent_3324_);
lean_dec(v_mantissa_3323_);
lean_dec_ref(v_a_3283_);
goto v___jp_3285_;
}
}
else
{
lean_dec(v_val_3321_);
lean_dec_ref(v_a_3283_);
goto v___jp_3285_;
}
}
else
{
lean_dec(v___x_3320_);
lean_dec_ref(v_a_3283_);
goto v___jp_3285_;
}
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec_ref(v_a_3283_);
v___x_3516_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__9));
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
return v___x_3517_;
}
v___jp_3285_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
v___jp_3288_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
v___jp_3291_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
return v___x_3296_;
}
v___jp_3297_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
v___jp_3300_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
return v___x_3302_;
}
v___jp_3303_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
v___jp_3306_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
v___jp_3309_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
v___jp_3312_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
v___jp_3315_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__1));
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___boxed(lean_object* v_json_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v_json_3518_, v_a_3519_);
lean_dec(v_json_3518_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(lean_object* v_json_3528_, lean_object* v_a_3529_){
_start:
{
if (lean_obj_tag(v_json_3528_) == 5)
{
lean_object* v_kvPairs_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_kvPairs_3555_ = lean_ctor_get(v_json_3528_, 0);
v___x_3556_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3556_);
if (lean_obj_tag(v___x_3557_) == 1)
{
lean_object* v_val_3558_; 
v_val_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_val_3558_);
lean_dec_ref_known(v___x_3557_, 1);
if (lean_obj_tag(v_val_3558_) == 2)
{
lean_object* v_n_3559_; lean_object* v_mantissa_3560_; lean_object* v_exponent_3561_; lean_object* v_natZero_3562_; lean_object* v_intZero_3563_; uint8_t v_isNeg_3564_; 
v_n_3559_ = lean_ctor_get(v_val_3558_, 0);
lean_inc_ref(v_n_3559_);
lean_dec_ref_known(v_val_3558_, 1);
v_mantissa_3560_ = lean_ctor_get(v_n_3559_, 0);
lean_inc(v_mantissa_3560_);
v_exponent_3561_ = lean_ctor_get(v_n_3559_, 1);
lean_inc(v_exponent_3561_);
lean_dec_ref(v_n_3559_);
v_natZero_3562_ = lean_unsigned_to_nat(0u);
v_intZero_3563_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3564_ = lean_int_dec_lt(v_mantissa_3560_, v_intZero_3563_);
if (v_isNeg_3564_ == 0)
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_nat_dec_eq(v_exponent_3561_, v_natZero_3562_);
lean_dec(v_exponent_3561_);
if (v___x_3565_ == 0)
{
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3531_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3567_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3566_);
if (lean_obj_tag(v___x_3567_) == 1)
{
lean_object* v_val_3568_; 
v_val_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_val_3568_);
lean_dec_ref_known(v___x_3567_, 1);
if (lean_obj_tag(v_val_3568_) == 4)
{
lean_object* v_elems_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_elems_3569_ = lean_ctor_get(v_val_3568_, 0);
lean_inc_ref(v_elems_3569_);
lean_dec_ref_known(v_val_3568_, 1);
v___x_3570_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 1)
{
lean_object* v_val_3572_; 
v_val_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___x_3571_, 1);
if (lean_obj_tag(v_val_3572_) == 2)
{
lean_object* v_n_3573_; lean_object* v_mantissa_3574_; lean_object* v_exponent_3575_; uint8_t v_isNeg_3576_; 
v_n_3573_ = lean_ctor_get(v_val_3572_, 0);
lean_inc_ref(v_n_3573_);
lean_dec_ref_known(v_val_3572_, 1);
v_mantissa_3574_ = lean_ctor_get(v_n_3573_, 0);
lean_inc(v_mantissa_3574_);
v_exponent_3575_ = lean_ctor_get(v_n_3573_, 1);
lean_inc(v_exponent_3575_);
lean_dec_ref(v_n_3573_);
v_isNeg_3576_ = lean_int_dec_lt(v_mantissa_3574_, v_intZero_3563_);
if (v_isNeg_3576_ == 0)
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_nat_dec_eq(v_exponent_3575_, v_natZero_3562_);
lean_dec(v_exponent_3575_);
if (v___x_3577_ == 0)
{
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3537_;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__2));
v___x_3579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3578_);
if (lean_obj_tag(v___x_3579_) == 1)
{
lean_object* v_val_3580_; 
v_val_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3580_);
lean_dec_ref_known(v___x_3579_, 1);
if (lean_obj_tag(v_val_3580_) == 2)
{
lean_object* v_n_3581_; lean_object* v_mantissa_3582_; lean_object* v_exponent_3583_; uint8_t v_isNeg_3584_; 
v_n_3581_ = lean_ctor_get(v_val_3580_, 0);
lean_inc_ref(v_n_3581_);
lean_dec_ref_known(v_val_3580_, 1);
v_mantissa_3582_ = lean_ctor_get(v_n_3581_, 0);
lean_inc(v_mantissa_3582_);
v_exponent_3583_ = lean_ctor_get(v_n_3581_, 1);
lean_inc(v_exponent_3583_);
lean_dec_ref(v_n_3581_);
v_isNeg_3584_ = lean_int_dec_lt(v_mantissa_3582_, v_intZero_3563_);
if (v_isNeg_3584_ == 0)
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_nat_dec_eq(v_exponent_3583_, v_natZero_3562_);
lean_dec(v_exponent_3583_);
if (v___x_3585_ == 0)
{
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3540_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__3));
v___x_3587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3586_);
if (lean_obj_tag(v___x_3587_) == 1)
{
lean_object* v_val_3588_; 
v_val_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_val_3588_);
lean_dec_ref_known(v___x_3587_, 1);
if (lean_obj_tag(v_val_3588_) == 2)
{
lean_object* v_n_3589_; lean_object* v_mantissa_3590_; lean_object* v_exponent_3591_; uint8_t v_isNeg_3592_; 
v_n_3589_ = lean_ctor_get(v_val_3588_, 0);
lean_inc_ref(v_n_3589_);
lean_dec_ref_known(v_val_3588_, 1);
v_mantissa_3590_ = lean_ctor_get(v_n_3589_, 0);
lean_inc(v_mantissa_3590_);
v_exponent_3591_ = lean_ctor_get(v_n_3589_, 1);
lean_inc(v_exponent_3591_);
lean_dec_ref(v_n_3589_);
v_isNeg_3592_ = lean_int_dec_lt(v_mantissa_3590_, v_intZero_3563_);
if (v_isNeg_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_eq(v_exponent_3591_, v_natZero_3562_);
lean_dec(v_exponent_3591_);
if (v___x_3593_ == 0)
{
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3543_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3594_);
if (lean_obj_tag(v___x_3595_) == 1)
{
lean_object* v_val_3596_; 
v_val_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_val_3596_);
lean_dec_ref_known(v___x_3595_, 1);
if (lean_obj_tag(v_val_3596_) == 2)
{
lean_object* v_n_3597_; lean_object* v_mantissa_3598_; lean_object* v_exponent_3599_; uint8_t v_isNeg_3600_; 
v_n_3597_ = lean_ctor_get(v_val_3596_, 0);
lean_inc_ref(v_n_3597_);
lean_dec_ref_known(v_val_3596_, 1);
v_mantissa_3598_ = lean_ctor_get(v_n_3597_, 0);
lean_inc(v_mantissa_3598_);
v_exponent_3599_ = lean_ctor_get(v_n_3597_, 1);
lean_inc(v_exponent_3599_);
lean_dec_ref(v_n_3597_);
v_isNeg_3600_ = lean_int_dec_lt(v_mantissa_3598_, v_intZero_3563_);
if (v_isNeg_3600_ == 0)
{
uint8_t v___x_3601_; 
v___x_3601_ = lean_nat_dec_eq(v_exponent_3599_, v_natZero_3562_);
lean_dec(v_exponent_3599_);
if (v___x_3601_ == 0)
{
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3546_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__4));
v___x_3603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3602_);
if (lean_obj_tag(v___x_3603_) == 1)
{
lean_object* v_val_3604_; 
v_val_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v___x_3603_, 1);
if (lean_obj_tag(v_val_3604_) == 2)
{
lean_object* v_n_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3731_; 
v_n_3605_ = lean_ctor_get(v_val_3604_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_val_3604_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3607_ = v_val_3604_;
v_isShared_3608_ = v_isSharedCheck_3731_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_n_3605_);
lean_dec(v_val_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3731_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v_mantissa_3609_; lean_object* v_exponent_3610_; uint8_t v_isNeg_3611_; 
v_mantissa_3609_ = lean_ctor_get(v_n_3605_, 0);
lean_inc(v_mantissa_3609_);
v_exponent_3610_ = lean_ctor_get(v_n_3605_, 1);
lean_inc(v_exponent_3610_);
lean_dec_ref(v_n_3605_);
v_isNeg_3611_ = lean_int_dec_lt(v_mantissa_3609_, v_intZero_3563_);
if (v_isNeg_3611_ == 0)
{
uint8_t v___x_3612_; 
v___x_3612_ = lean_nat_dec_eq(v_exponent_3610_, v_natZero_3562_);
lean_dec(v_exponent_3610_);
if (v___x_3612_ == 0)
{
lean_dec(v_mantissa_3609_);
lean_del_object(v___x_3607_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3549_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3555_, v___x_3613_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3730_; 
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3730_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3730_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
if (lean_obj_tag(v_val_3615_) == 1)
{
uint8_t v_b_3619_; lean_object* v_nameMap_3620_; lean_object* v_a_3621_; lean_object* v___x_3622_; 
v_b_3619_ = lean_ctor_get_uint8(v_val_3615_, 0);
lean_dec_ref_known(v_val_3615_, 0);
v_nameMap_3620_ = lean_ctor_get(v_a_3529_, 1);
v_a_3621_ = lean_nat_abs(v_mantissa_3560_);
lean_dec(v_mantissa_3560_);
v___x_3622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3620_, v_a_3621_);
if (lean_obj_tag(v___x_3622_) == 1)
{
lean_object* v_val_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_a_3621_);
lean_del_object(v___x_3617_);
lean_del_object(v___x_3607_);
v_val_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3720_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_val_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3720_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3569_, v_a_3529_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3711_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3711_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3711_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_snd_3632_; lean_object* v_fst_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3710_; 
v_snd_3632_ = lean_ctor_get(v_a_3628_, 1);
v_fst_3633_ = lean_ctor_get(v_a_3628_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_a_3628_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3635_ = v_a_3628_;
v_isShared_3636_ = v_isSharedCheck_3710_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_snd_3632_);
lean_inc(v_fst_3633_);
lean_dec(v_a_3628_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3710_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_stream_3637_; lean_object* v_nameMap_3638_; lean_object* v_levelMap_3639_; lean_object* v_exprMap_3640_; lean_object* v_recursorRuleMap_3641_; lean_object* v_constMap_3642_; lean_object* v_constOrder_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3709_; 
v_stream_3637_ = lean_ctor_get(v_snd_3632_, 0);
v_nameMap_3638_ = lean_ctor_get(v_snd_3632_, 1);
v_levelMap_3639_ = lean_ctor_get(v_snd_3632_, 2);
v_exprMap_3640_ = lean_ctor_get(v_snd_3632_, 3);
v_recursorRuleMap_3641_ = lean_ctor_get(v_snd_3632_, 4);
v_constMap_3642_ = lean_ctor_get(v_snd_3632_, 5);
v_constOrder_3643_ = lean_ctor_get(v_snd_3632_, 6);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_snd_3632_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3645_ = v_snd_3632_;
v_isShared_3646_ = v_isSharedCheck_3709_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_constOrder_3643_);
lean_inc(v_constMap_3642_);
lean_inc(v_recursorRuleMap_3641_);
lean_inc(v_exprMap_3640_);
lean_inc(v_levelMap_3639_);
lean_inc(v_nameMap_3638_);
lean_inc(v_stream_3637_);
lean_dec(v_snd_3632_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3709_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_a_3647_; lean_object* v___x_3648_; 
v_a_3647_ = lean_nat_abs(v_mantissa_3574_);
lean_dec(v_mantissa_3574_);
v___x_3648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3640_, v_a_3647_);
if (lean_obj_tag(v___x_3648_) == 1)
{
lean_object* v_val_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_a_3647_);
lean_del_object(v___x_3625_);
v_val_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3699_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_val_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3699_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_a_3653_; lean_object* v___x_3654_; 
v_a_3653_ = lean_nat_abs(v_mantissa_3582_);
lean_dec(v_mantissa_3582_);
v___x_3654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3638_, v_a_3653_);
if (lean_obj_tag(v___x_3654_) == 1)
{
lean_object* v_val_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_a_3653_);
lean_del_object(v___x_3651_);
v_val_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3689_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_val_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3689_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
uint8_t v___x_3659_; 
v___x_3659_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_3642_, v_val_3623_);
if (v___x_3659_ == 0)
{
lean_object* v_a_3660_; lean_object* v_a_3661_; lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v_a_3660_ = lean_nat_abs(v_mantissa_3590_);
lean_dec(v_mantissa_3590_);
v_a_3661_ = lean_nat_abs(v_mantissa_3598_);
lean_dec(v_mantissa_3598_);
v_a_3662_ = lean_nat_abs(v_mantissa_3609_);
lean_dec(v_mantissa_3609_);
lean_inc(v_val_3623_);
v___x_3663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3663_, 0, v_val_3623_);
lean_ctor_set(v___x_3663_, 1, v_fst_3633_);
lean_ctor_set(v___x_3663_, 2, v_val_3649_);
v___x_3664_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v_val_3655_);
lean_ctor_set(v___x_3664_, 2, v_a_3660_);
lean_ctor_set(v___x_3664_, 3, v_a_3661_);
lean_ctor_set(v___x_3664_, 4, v_a_3662_);
lean_ctor_set_uint8(v___x_3664_, sizeof(void*)*5, v_b_3619_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 6);
lean_ctor_set(v___x_3657_, 0, v___x_3664_);
v___x_3666_ = v___x_3657_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3667_ = lean_box(0);
lean_inc(v_val_3623_);
v___x_3668_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_3642_, v_val_3623_, v___x_3666_);
v___x_3669_ = lean_array_push(v_constOrder_3643_, v_val_3623_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 6, v___x_3669_);
lean_ctor_set(v___x_3645_, 5, v___x_3668_);
v___x_3671_ = v___x_3645_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_stream_3637_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_nameMap_3638_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_levelMap_3639_);
lean_ctor_set(v_reuseFailAlloc_3678_, 3, v_exprMap_3640_);
lean_ctor_set(v_reuseFailAlloc_3678_, 4, v_recursorRuleMap_3641_);
lean_ctor_set(v_reuseFailAlloc_3678_, 5, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3678_, 6, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3671_);
lean_ctor_set(v___x_3635_, 0, v___x_3667_);
v___x_3673_ = v___x_3635_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3673_);
v___x_3675_ = v___x_3630_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
lean_dec(v_val_3655_);
lean_dec(v_val_3649_);
lean_del_object(v___x_3645_);
lean_dec_ref(v_constOrder_3643_);
lean_dec_ref(v_constMap_3642_);
lean_dec_ref(v_recursorRuleMap_3641_);
lean_dec_ref(v_exprMap_3640_);
lean_dec_ref(v_levelMap_3639_);
lean_dec_ref(v_nameMap_3638_);
lean_dec_ref(v_stream_3637_);
lean_del_object(v___x_3635_);
lean_dec(v_fst_3633_);
lean_dec(v_mantissa_3609_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
v___x_3680_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_3681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3623_, v___x_3659_);
v___x_3682_ = lean_string_append(v___x_3680_, v___x_3681_);
lean_dec_ref(v___x_3681_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 18);
lean_ctor_set(v___x_3657_, 0, v___x_3682_);
v___x_3684_ = v___x_3657_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3686_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3684_);
v___x_3686_ = v___x_3630_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_dec(v___x_3654_);
lean_dec(v_val_3649_);
lean_del_object(v___x_3645_);
lean_dec_ref(v_constOrder_3643_);
lean_dec_ref(v_constMap_3642_);
lean_dec_ref(v_recursorRuleMap_3641_);
lean_dec_ref(v_exprMap_3640_);
lean_dec_ref(v_levelMap_3639_);
lean_dec_ref(v_nameMap_3638_);
lean_dec_ref(v_stream_3637_);
lean_del_object(v___x_3635_);
lean_dec(v_fst_3633_);
lean_dec(v_val_3623_);
lean_dec(v_mantissa_3609_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
v___x_3690_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3691_ = l_Nat_reprFast(v_a_3653_);
v___x_3692_ = lean_string_append(v___x_3690_, v___x_3691_);
lean_dec_ref(v___x_3691_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 18);
lean_ctor_set(v___x_3651_, 0, v___x_3692_);
v___x_3694_ = v___x_3651_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3696_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3694_);
v___x_3696_ = v___x_3630_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_dec(v___x_3648_);
lean_del_object(v___x_3645_);
lean_dec_ref(v_constOrder_3643_);
lean_dec_ref(v_constMap_3642_);
lean_dec_ref(v_recursorRuleMap_3641_);
lean_dec_ref(v_exprMap_3640_);
lean_dec_ref(v_levelMap_3639_);
lean_dec_ref(v_nameMap_3638_);
lean_dec_ref(v_stream_3637_);
lean_del_object(v___x_3635_);
lean_dec(v_fst_3633_);
lean_dec(v_val_3623_);
lean_dec(v_mantissa_3609_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
v___x_3700_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3701_ = l_Nat_reprFast(v_a_3647_);
v___x_3702_ = lean_string_append(v___x_3700_, v___x_3701_);
lean_dec_ref(v___x_3701_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 18);
lean_ctor_set(v___x_3625_, 0, v___x_3702_);
v___x_3704_ = v___x_3625_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3704_);
v___x_3706_ = v___x_3630_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3625_);
lean_dec(v_val_3623_);
lean_dec(v_mantissa_3609_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
v_a_3712_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3627_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3627_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3725_; 
lean_dec(v___x_3622_);
lean_dec(v_mantissa_3609_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec_ref(v_a_3529_);
v___x_3721_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3722_ = l_Nat_reprFast(v_a_3621_);
v___x_3723_ = lean_string_append(v___x_3721_, v___x_3722_);
lean_dec_ref(v___x_3722_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 18);
lean_ctor_set(v___x_3617_, 0, v___x_3723_);
v___x_3725_ = v___x_3617_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 1);
lean_ctor_set(v___x_3607_, 0, v___x_3725_);
v___x_3727_ = v___x_3607_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_del_object(v___x_3617_);
lean_dec(v_val_3615_);
lean_dec(v_mantissa_3609_);
lean_del_object(v___x_3607_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3552_;
}
}
}
else
{
lean_dec(v___x_3614_);
lean_dec(v_mantissa_3609_);
lean_del_object(v___x_3607_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3552_;
}
}
}
else
{
lean_dec(v_exponent_3610_);
lean_dec(v_mantissa_3609_);
lean_del_object(v___x_3607_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3549_;
}
}
}
else
{
lean_dec(v_val_3604_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3549_;
}
}
else
{
lean_dec(v___x_3603_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3549_;
}
}
}
else
{
lean_dec(v_exponent_3599_);
lean_dec(v_mantissa_3598_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3546_;
}
}
else
{
lean_dec(v_val_3596_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3546_;
}
}
else
{
lean_dec(v___x_3595_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3546_;
}
}
}
else
{
lean_dec(v_exponent_3591_);
lean_dec(v_mantissa_3590_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3543_;
}
}
else
{
lean_dec(v_val_3588_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3543_;
}
}
else
{
lean_dec(v___x_3587_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3543_;
}
}
}
else
{
lean_dec(v_exponent_3583_);
lean_dec(v_mantissa_3582_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3540_;
}
}
else
{
lean_dec(v_val_3580_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3540_;
}
}
else
{
lean_dec(v___x_3579_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3540_;
}
}
}
else
{
lean_dec(v_exponent_3575_);
lean_dec(v_mantissa_3574_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3537_;
}
}
else
{
lean_dec(v_val_3572_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3537_;
}
}
else
{
lean_dec(v___x_3571_);
lean_dec_ref(v_elems_3569_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3537_;
}
}
else
{
lean_dec(v_val_3568_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3534_;
}
}
else
{
lean_dec(v___x_3567_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3534_;
}
}
}
else
{
lean_dec(v_exponent_3561_);
lean_dec(v_mantissa_3560_);
lean_dec_ref(v_a_3529_);
goto v___jp_3531_;
}
}
else
{
lean_dec(v_val_3558_);
lean_dec_ref(v_a_3529_);
goto v___jp_3531_;
}
}
else
{
lean_dec(v___x_3557_);
lean_dec_ref(v_a_3529_);
goto v___jp_3531_;
}
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_dec_ref(v_a_3529_);
v___x_3732_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
return v___x_3733_;
}
v___jp_3531_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
v___jp_3534_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
v___jp_3537_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
v___jp_3540_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
return v___x_3542_;
}
v___jp_3543_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
v___jp_3546_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
v___jp_3549_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
v___jp_3552_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___closed__1));
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo___boxed(lean_object* v_json_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v_json_3734_, v_a_3735_);
lean_dec(v_json_3734_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(lean_object* v_x_3743_, lean_object* v_x_3744_, lean_object* v___y_3745_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = l_List_reverse___redArg(v_x_3744_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___y_3745_);
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
return v___x_3758_;
}
else
{
lean_object* v_head_3759_; 
v_head_3759_ = lean_ctor_get(v_x_3743_, 0);
lean_inc(v_head_3759_);
if (lean_obj_tag(v_head_3759_) == 5)
{
lean_object* v_tail_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3835_; 
v_tail_3760_ = lean_ctor_get(v_x_3743_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_x_3743_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v_x_3743_, 0);
lean_dec(v_unused_3836_);
v___x_3762_ = v_x_3743_;
v_isShared_3763_ = v_isSharedCheck_3835_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_tail_3760_);
lean_dec(v_x_3743_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3835_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v_kvPairs_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_kvPairs_3764_ = lean_ctor_get(v_head_3759_, 0);
lean_inc(v_kvPairs_3764_);
lean_dec_ref_known(v_head_3759_, 1);
v___x_3765_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo___closed__3));
v___x_3766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3764_, v___x_3765_);
if (lean_obj_tag(v___x_3766_) == 1)
{
lean_object* v_val_3767_; 
v_val_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_val_3767_);
lean_dec_ref_known(v___x_3766_, 1);
if (lean_obj_tag(v_val_3767_) == 2)
{
lean_object* v_n_3768_; lean_object* v_mantissa_3769_; lean_object* v_exponent_3770_; lean_object* v_natZero_3771_; lean_object* v_intZero_3772_; uint8_t v_isNeg_3773_; 
v_n_3768_ = lean_ctor_get(v_val_3767_, 0);
lean_inc_ref(v_n_3768_);
lean_dec_ref_known(v_val_3767_, 1);
v_mantissa_3769_ = lean_ctor_get(v_n_3768_, 0);
lean_inc(v_mantissa_3769_);
v_exponent_3770_ = lean_ctor_get(v_n_3768_, 1);
lean_inc(v_exponent_3770_);
lean_dec_ref(v_n_3768_);
v_natZero_3771_ = lean_unsigned_to_nat(0u);
v_intZero_3772_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3773_ = lean_int_dec_lt(v_mantissa_3769_, v_intZero_3772_);
if (v_isNeg_3773_ == 0)
{
uint8_t v___x_3774_; 
v___x_3774_ = lean_nat_dec_eq(v_exponent_3770_, v_natZero_3771_);
lean_dec(v_exponent_3770_);
if (v___x_3774_ == 0)
{
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3747_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__2));
v___x_3776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3764_, v___x_3775_);
if (lean_obj_tag(v___x_3776_) == 1)
{
lean_object* v_val_3777_; 
v_val_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v___x_3776_, 1);
if (lean_obj_tag(v_val_3777_) == 2)
{
lean_object* v_n_3778_; lean_object* v_mantissa_3779_; lean_object* v_exponent_3780_; uint8_t v_isNeg_3781_; 
v_n_3778_ = lean_ctor_get(v_val_3777_, 0);
lean_inc_ref(v_n_3778_);
lean_dec_ref_known(v_val_3777_, 1);
v_mantissa_3779_ = lean_ctor_get(v_n_3778_, 0);
lean_inc(v_mantissa_3779_);
v_exponent_3780_ = lean_ctor_get(v_n_3778_, 1);
lean_inc(v_exponent_3780_);
lean_dec_ref(v_n_3778_);
v_isNeg_3781_ = lean_int_dec_lt(v_mantissa_3779_, v_intZero_3772_);
if (v_isNeg_3781_ == 0)
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_nat_dec_eq(v_exponent_3780_, v_natZero_3771_);
lean_dec(v_exponent_3780_);
if (v___x_3782_ == 0)
{
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3750_;
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__3));
v___x_3784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3764_, v___x_3783_);
lean_dec(v_kvPairs_3764_);
if (lean_obj_tag(v___x_3784_) == 1)
{
lean_object* v_val_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3834_; 
v_val_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3834_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_val_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3834_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
if (lean_obj_tag(v_val_3785_) == 2)
{
lean_object* v_n_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3833_; 
v_n_3789_ = lean_ctor_get(v_val_3785_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_val_3785_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3791_ = v_val_3785_;
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_n_3789_);
lean_dec(v_val_3785_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_mantissa_3793_; lean_object* v_exponent_3794_; uint8_t v_isNeg_3795_; 
v_mantissa_3793_ = lean_ctor_get(v_n_3789_, 0);
lean_inc(v_mantissa_3793_);
v_exponent_3794_ = lean_ctor_get(v_n_3789_, 1);
lean_inc(v_exponent_3794_);
lean_dec_ref(v_n_3789_);
v_isNeg_3795_ = lean_int_dec_lt(v_mantissa_3793_, v_intZero_3772_);
if (v_isNeg_3795_ == 0)
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_nat_dec_eq(v_exponent_3794_, v_natZero_3771_);
lean_dec(v_exponent_3794_);
if (v___x_3796_ == 0)
{
lean_dec(v_mantissa_3793_);
lean_del_object(v___x_3791_);
lean_del_object(v___x_3787_);
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3753_;
}
else
{
lean_object* v_nameMap_3797_; lean_object* v_exprMap_3798_; lean_object* v_a_3799_; lean_object* v___x_3800_; 
v_nameMap_3797_ = lean_ctor_get(v___y_3745_, 1);
v_exprMap_3798_ = lean_ctor_get(v___y_3745_, 3);
v_a_3799_ = lean_nat_abs(v_mantissa_3769_);
lean_dec(v_mantissa_3769_);
v___x_3800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3797_, v_a_3799_);
if (lean_obj_tag(v___x_3800_) == 1)
{
lean_object* v_val_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v_a_3799_);
lean_del_object(v___x_3787_);
v_val_3801_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3803_ = v___x_3800_;
v_isShared_3804_ = v_isSharedCheck_3823_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_val_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3823_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_nat_abs(v_mantissa_3793_);
lean_dec(v_mantissa_3793_);
v___x_3806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3798_, v_a_3805_);
if (lean_obj_tag(v___x_3806_) == 1)
{
lean_object* v_val_3807_; lean_object* v_a_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec(v_a_3805_);
lean_del_object(v___x_3803_);
lean_del_object(v___x_3791_);
v_val_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_val_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v_a_3808_ = lean_nat_abs(v_mantissa_3779_);
lean_dec(v_mantissa_3779_);
v___x_3809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3809_, 0, v_val_3801_);
lean_ctor_set(v___x_3809_, 1, v_a_3808_);
lean_ctor_set(v___x_3809_, 2, v_val_3807_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 1, v_x_3744_);
lean_ctor_set(v___x_3762_, 0, v___x_3809_);
v___x_3811_ = v___x_3762_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_x_3744_);
v___x_3811_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v_x_3743_ = v_tail_3760_;
v_x_3744_ = v___x_3811_;
goto _start;
}
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_dec(v___x_3806_);
lean_dec(v_val_3801_);
lean_dec(v_mantissa_3779_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
v___x_3814_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_3815_ = l_Nat_reprFast(v_a_3805_);
v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
lean_dec_ref(v___x_3815_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 18);
lean_ctor_set(v___x_3803_, 0, v___x_3816_);
v___x_3818_ = v___x_3803_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3820_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set_tag(v___x_3791_, 1);
lean_ctor_set(v___x_3791_, 0, v___x_3818_);
v___x_3820_ = v___x_3791_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3828_; 
lean_dec(v___x_3800_);
lean_dec(v_mantissa_3793_);
lean_dec(v_mantissa_3779_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
v___x_3824_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_3825_ = l_Nat_reprFast(v_a_3799_);
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
lean_dec_ref(v___x_3825_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set_tag(v___x_3791_, 18);
lean_ctor_set(v___x_3791_, 0, v___x_3826_);
v___x_3828_ = v___x_3791_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3828_);
v___x_3830_ = v___x_3787_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
else
{
lean_dec(v_exponent_3794_);
lean_dec(v_mantissa_3793_);
lean_del_object(v___x_3791_);
lean_del_object(v___x_3787_);
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3753_;
}
}
}
else
{
lean_del_object(v___x_3787_);
lean_dec(v_val_3785_);
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3753_;
}
}
}
else
{
lean_dec(v___x_3784_);
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3753_;
}
}
}
else
{
lean_dec(v_exponent_3780_);
lean_dec(v_mantissa_3779_);
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3750_;
}
}
else
{
lean_dec(v_val_3777_);
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3750_;
}
}
else
{
lean_dec(v___x_3776_);
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3750_;
}
}
}
else
{
lean_dec(v_exponent_3770_);
lean_dec(v_mantissa_3769_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3747_;
}
}
else
{
lean_dec(v_val_3767_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3747_;
}
}
else
{
lean_dec(v___x_3766_);
lean_dec(v_kvPairs_3764_);
lean_del_object(v___x_3762_);
lean_dec(v_tail_3760_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
goto v___jp_3747_;
}
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec_ref_known(v_x_3743_, 2);
lean_dec(v_head_3759_);
lean_dec_ref(v___y_3745_);
lean_dec(v_x_3744_);
v___x_3837_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
}
v___jp_3747_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
v___jp_3750_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
return v___x_3752_;
}
v___jp_3753_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___boxed(lean_object* v_x_3839_, lean_object* v_x_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v_x_3839_, v_x_3840_, v___y_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(lean_object* v_json_3848_, lean_object* v_a_3849_){
_start:
{
if (lean_obj_tag(v_json_3848_) == 5)
{
lean_object* v_kvPairs_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_kvPairs_3884_ = lean_ctor_get(v_json_3848_, 0);
v___x_3885_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst___closed__0));
v___x_3886_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3885_);
if (lean_obj_tag(v___x_3886_) == 1)
{
lean_object* v_val_3887_; 
v_val_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_val_3887_);
lean_dec_ref_known(v___x_3886_, 1);
if (lean_obj_tag(v_val_3887_) == 2)
{
lean_object* v_n_3888_; lean_object* v_mantissa_3889_; lean_object* v_exponent_3890_; lean_object* v_natZero_3891_; lean_object* v_intZero_3892_; uint8_t v_isNeg_3893_; 
v_n_3888_ = lean_ctor_get(v_val_3887_, 0);
lean_inc_ref(v_n_3888_);
lean_dec_ref_known(v_val_3887_, 1);
v_mantissa_3889_ = lean_ctor_get(v_n_3888_, 0);
lean_inc(v_mantissa_3889_);
v_exponent_3890_ = lean_ctor_get(v_n_3888_, 1);
lean_inc(v_exponent_3890_);
lean_dec_ref(v_n_3888_);
v_natZero_3891_ = lean_unsigned_to_nat(0u);
v_intZero_3892_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_3893_ = lean_int_dec_lt(v_mantissa_3889_, v_intZero_3892_);
if (v_isNeg_3893_ == 0)
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_nat_dec_eq(v_exponent_3890_, v_natZero_3891_);
lean_dec(v_exponent_3890_);
if (v___x_3894_ == 0)
{
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3851_;
}
else
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__2));
v___x_3896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3895_);
if (lean_obj_tag(v___x_3896_) == 1)
{
lean_object* v_val_3897_; 
v_val_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_val_3897_);
lean_dec_ref_known(v___x_3896_, 1);
if (lean_obj_tag(v_val_3897_) == 4)
{
lean_object* v_elems_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_elems_3898_ = lean_ctor_get(v_val_3897_, 0);
lean_inc_ref(v_elems_3898_);
lean_dec_ref_known(v_val_3897_, 1);
v___x_3899_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam___closed__2));
v___x_3900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3899_);
if (lean_obj_tag(v___x_3900_) == 1)
{
lean_object* v_val_3901_; 
v_val_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v___x_3900_, 1);
if (lean_obj_tag(v_val_3901_) == 2)
{
lean_object* v_n_3902_; lean_object* v_mantissa_3903_; lean_object* v_exponent_3904_; uint8_t v_isNeg_3905_; 
v_n_3902_ = lean_ctor_get(v_val_3901_, 0);
lean_inc_ref(v_n_3902_);
lean_dec_ref_known(v_val_3901_, 1);
v_mantissa_3903_ = lean_ctor_get(v_n_3902_, 0);
lean_inc(v_mantissa_3903_);
v_exponent_3904_ = lean_ctor_get(v_n_3902_, 1);
lean_inc(v_exponent_3904_);
lean_dec_ref(v_n_3902_);
v_isNeg_3905_ = lean_int_dec_lt(v_mantissa_3903_, v_intZero_3892_);
if (v_isNeg_3905_ == 0)
{
uint8_t v___x_3906_; 
v___x_3906_ = lean_nat_dec_eq(v_exponent_3904_, v_natZero_3891_);
lean_dec(v_exponent_3904_);
if (v___x_3906_ == 0)
{
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3857_;
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__4));
v___x_3908_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3907_);
if (lean_obj_tag(v___x_3908_) == 1)
{
lean_object* v_val_3909_; 
v_val_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v___x_3908_, 1);
if (lean_obj_tag(v_val_3909_) == 4)
{
lean_object* v_elems_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_elems_3910_ = lean_ctor_get(v_val_3909_, 0);
lean_inc_ref(v_elems_3910_);
lean_dec_ref_known(v_val_3909_, 1);
v___x_3911_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__2));
v___x_3912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3911_);
if (lean_obj_tag(v___x_3912_) == 1)
{
lean_object* v_val_3913_; 
v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v___x_3912_, 1);
if (lean_obj_tag(v_val_3913_) == 2)
{
lean_object* v_n_3914_; lean_object* v_mantissa_3915_; lean_object* v_exponent_3916_; uint8_t v_isNeg_3917_; 
v_n_3914_ = lean_ctor_get(v_val_3913_, 0);
lean_inc_ref(v_n_3914_);
lean_dec_ref_known(v_val_3913_, 1);
v_mantissa_3915_ = lean_ctor_get(v_n_3914_, 0);
lean_inc(v_mantissa_3915_);
v_exponent_3916_ = lean_ctor_get(v_n_3914_, 1);
lean_inc(v_exponent_3916_);
lean_dec_ref(v_n_3914_);
v_isNeg_3917_ = lean_int_dec_lt(v_mantissa_3915_, v_intZero_3892_);
if (v_isNeg_3917_ == 0)
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_nat_dec_eq(v_exponent_3916_, v_natZero_3891_);
lean_dec(v_exponent_3916_);
if (v___x_3918_ == 0)
{
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3863_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__3));
v___x_3920_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3919_);
if (lean_obj_tag(v___x_3920_) == 1)
{
lean_object* v_val_3921_; 
v_val_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_val_3921_);
lean_dec_ref_known(v___x_3920_, 1);
if (lean_obj_tag(v_val_3921_) == 2)
{
lean_object* v_n_3922_; lean_object* v_mantissa_3923_; lean_object* v_exponent_3924_; uint8_t v_isNeg_3925_; 
v_n_3922_ = lean_ctor_get(v_val_3921_, 0);
lean_inc_ref(v_n_3922_);
lean_dec_ref_known(v_val_3921_, 1);
v_mantissa_3923_ = lean_ctor_get(v_n_3922_, 0);
lean_inc(v_mantissa_3923_);
v_exponent_3924_ = lean_ctor_get(v_n_3922_, 1);
lean_inc(v_exponent_3924_);
lean_dec_ref(v_n_3922_);
v_isNeg_3925_ = lean_int_dec_lt(v_mantissa_3923_, v_intZero_3892_);
if (v_isNeg_3925_ == 0)
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_eq(v_exponent_3924_, v_natZero_3891_);
lean_dec(v_exponent_3924_);
if (v___x_3926_ == 0)
{
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3866_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__0));
v___x_3928_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3927_);
if (lean_obj_tag(v___x_3928_) == 1)
{
lean_object* v_val_3929_; 
v_val_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_val_3929_);
lean_dec_ref_known(v___x_3928_, 1);
if (lean_obj_tag(v_val_3929_) == 2)
{
lean_object* v_n_3930_; lean_object* v_mantissa_3931_; lean_object* v_exponent_3932_; uint8_t v_isNeg_3933_; 
v_n_3930_ = lean_ctor_get(v_val_3929_, 0);
lean_inc_ref(v_n_3930_);
lean_dec_ref_known(v_val_3929_, 1);
v_mantissa_3931_ = lean_ctor_get(v_n_3930_, 0);
lean_inc(v_mantissa_3931_);
v_exponent_3932_ = lean_ctor_get(v_n_3930_, 1);
lean_inc(v_exponent_3932_);
lean_dec_ref(v_n_3930_);
v_isNeg_3933_ = lean_int_dec_lt(v_mantissa_3931_, v_intZero_3892_);
if (v_isNeg_3933_ == 0)
{
uint8_t v___x_3934_; 
v___x_3934_ = lean_nat_dec_eq(v_exponent_3932_, v_natZero_3891_);
lean_dec(v_exponent_3932_);
if (v___x_3934_ == 0)
{
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3869_;
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__1));
v___x_3936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3935_);
if (lean_obj_tag(v___x_3936_) == 1)
{
lean_object* v_val_3937_; 
v_val_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_val_3937_);
lean_dec_ref_known(v___x_3936_, 1);
if (lean_obj_tag(v_val_3937_) == 2)
{
lean_object* v_n_3938_; lean_object* v_mantissa_3939_; lean_object* v_exponent_3940_; uint8_t v_isNeg_3941_; 
v_n_3938_ = lean_ctor_get(v_val_3937_, 0);
lean_inc_ref(v_n_3938_);
lean_dec_ref_known(v_val_3937_, 1);
v_mantissa_3939_ = lean_ctor_get(v_n_3938_, 0);
lean_inc(v_mantissa_3939_);
v_exponent_3940_ = lean_ctor_get(v_n_3938_, 1);
lean_inc(v_exponent_3940_);
lean_dec_ref(v_n_3938_);
v_isNeg_3941_ = lean_int_dec_lt(v_mantissa_3939_, v_intZero_3892_);
if (v_isNeg_3941_ == 0)
{
uint8_t v___x_3942_; 
v___x_3942_ = lean_nat_dec_eq(v_exponent_3940_, v_natZero_3891_);
lean_dec(v_exponent_3940_);
if (v___x_3942_ == 0)
{
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3872_;
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__2));
v___x_3944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3943_);
if (lean_obj_tag(v___x_3944_) == 1)
{
lean_object* v_val_3945_; 
v_val_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v___x_3944_, 1);
if (lean_obj_tag(v_val_3945_) == 1)
{
uint8_t v_b_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_b_3946_ = lean_ctor_get_uint8(v_val_3945_, 0);
lean_dec_ref_known(v_val_3945_, 0);
v___x_3947_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___closed__3));
v___x_3948_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3947_);
if (lean_obj_tag(v___x_3948_) == 1)
{
lean_object* v_val_3949_; 
v_val_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_val_3949_);
lean_dec_ref_known(v___x_3948_, 1);
if (lean_obj_tag(v_val_3949_) == 4)
{
lean_object* v_elems_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4088_; 
v_elems_3950_ = lean_ctor_get(v_val_3949_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_val_3949_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_3952_ = v_val_3949_;
v_isShared_3953_ = v_isSharedCheck_4088_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_elems_3950_);
lean_dec(v_val_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4088_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo___closed__3));
v___x_3955_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_kvPairs_3884_, v___x_3954_);
if (lean_obj_tag(v___x_3955_) == 1)
{
lean_object* v_val_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_4087_; 
v_val_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_4087_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_val_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_4087_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
if (lean_obj_tag(v_val_3956_) == 1)
{
uint8_t v_b_3960_; lean_object* v_nameMap_3961_; lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_b_3960_ = lean_ctor_get_uint8(v_val_3956_, 0);
lean_dec_ref_known(v_val_3956_, 0);
v_nameMap_3961_ = lean_ctor_get(v_a_3849_, 1);
v_a_3962_ = lean_nat_abs(v_mantissa_3889_);
lean_dec(v_mantissa_3889_);
v___x_3963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_nameMap_3961_, v_a_3962_);
if (lean_obj_tag(v___x_3963_) == 1)
{
lean_object* v_val_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_a_3962_);
lean_del_object(v___x_3958_);
lean_del_object(v___x_3952_);
v_val_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_4077_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_val_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4077_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; 
v___x_3968_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3898_, v_a_3849_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4068_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_4068_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4068_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v_snd_3973_; lean_object* v_fst_3974_; lean_object* v_exprMap_3975_; lean_object* v_a_3976_; lean_object* v___x_3977_; 
v_snd_3973_ = lean_ctor_get(v_a_3969_, 1);
lean_inc(v_snd_3973_);
v_fst_3974_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_fst_3974_);
lean_dec(v_a_3969_);
v_exprMap_3975_ = lean_ctor_get(v_snd_3973_, 3);
v_a_3976_ = lean_nat_abs(v_mantissa_3903_);
lean_dec(v_mantissa_3903_);
v___x_3977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__1___redArg(v_exprMap_3975_, v_a_3976_);
if (lean_obj_tag(v___x_3977_) == 1)
{
lean_object* v_val_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_3976_);
lean_del_object(v___x_3971_);
lean_del_object(v___x_3966_);
v_val_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_4058_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_val_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4058_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; 
v___x_3982_ = l___private_LeanExport_Parse_0__LeanExport_Parse_getNameList(v_elems_3910_, v_snd_3973_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v_fst_3984_; lean_object* v_snd_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v_fst_3984_ = lean_ctor_get(v_a_3983_, 0);
lean_inc(v_fst_3984_);
v_snd_3985_ = lean_ctor_get(v_a_3983_, 1);
lean_inc(v_snd_3985_);
lean_dec(v_a_3983_);
v___x_3986_ = lean_array_to_list(v_elems_3950_);
v___x_3987_ = lean_box(0);
v___x_3988_ = l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0(v___x_3986_, v___x_3987_, v_snd_3985_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4041_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_3991_ = v___x_3988_;
v_isShared_3992_ = v_isSharedCheck_4041_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4041_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v_snd_3993_; lean_object* v_fst_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4040_; 
v_snd_3993_ = lean_ctor_get(v_a_3989_, 1);
v_fst_3994_ = lean_ctor_get(v_a_3989_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_a_3989_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_3996_ = v_a_3989_;
v_isShared_3997_ = v_isSharedCheck_4040_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_snd_3993_);
lean_inc(v_fst_3994_);
lean_dec(v_a_3989_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4040_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_stream_3998_; lean_object* v_nameMap_3999_; lean_object* v_levelMap_4000_; lean_object* v_exprMap_4001_; lean_object* v_recursorRuleMap_4002_; lean_object* v_constMap_4003_; lean_object* v_constOrder_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4039_; 
v_stream_3998_ = lean_ctor_get(v_snd_3993_, 0);
v_nameMap_3999_ = lean_ctor_get(v_snd_3993_, 1);
v_levelMap_4000_ = lean_ctor_get(v_snd_3993_, 2);
v_exprMap_4001_ = lean_ctor_get(v_snd_3993_, 3);
v_recursorRuleMap_4002_ = lean_ctor_get(v_snd_3993_, 4);
v_constMap_4003_ = lean_ctor_get(v_snd_3993_, 5);
v_constOrder_4004_ = lean_ctor_get(v_snd_3993_, 6);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_snd_3993_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4006_ = v_snd_3993_;
v_isShared_4007_ = v_isSharedCheck_4039_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_constOrder_4004_);
lean_inc(v_constMap_4003_);
lean_inc(v_recursorRuleMap_4002_);
lean_inc(v_exprMap_4001_);
lean_inc(v_levelMap_4000_);
lean_inc(v_nameMap_3999_);
lean_inc(v_stream_3998_);
lean_dec(v_snd_3993_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4039_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
uint8_t v___x_4008_; 
v___x_4008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__0___redArg(v_constMap_4003_, v_val_3964_);
if (v___x_4008_ == 0)
{
lean_object* v_a_4009_; lean_object* v_a_4010_; lean_object* v_a_4011_; lean_object* v_a_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4016_; 
v_a_4009_ = lean_nat_abs(v_mantissa_3915_);
lean_dec(v_mantissa_3915_);
v_a_4010_ = lean_nat_abs(v_mantissa_3923_);
lean_dec(v_mantissa_3923_);
v_a_4011_ = lean_nat_abs(v_mantissa_3931_);
lean_dec(v_mantissa_3931_);
v_a_4012_ = lean_nat_abs(v_mantissa_3939_);
lean_dec(v_mantissa_3939_);
lean_inc(v_val_3964_);
v___x_4013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4013_, 0, v_val_3964_);
lean_ctor_set(v___x_4013_, 1, v_fst_3974_);
lean_ctor_set(v___x_4013_, 2, v_val_3978_);
v___x_4014_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
lean_ctor_set(v___x_4014_, 1, v_fst_3984_);
lean_ctor_set(v___x_4014_, 2, v_a_4009_);
lean_ctor_set(v___x_4014_, 3, v_a_4010_);
lean_ctor_set(v___x_4014_, 4, v_a_4011_);
lean_ctor_set(v___x_4014_, 5, v_a_4012_);
lean_ctor_set(v___x_4014_, 6, v_fst_3994_);
lean_ctor_set_uint8(v___x_4014_, sizeof(void*)*7, v_b_3946_);
lean_ctor_set_uint8(v___x_4014_, sizeof(void*)*7 + 1, v_b_3960_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set_tag(v___x_3980_, 7);
lean_ctor_set(v___x_3980_, 0, v___x_4014_);
v___x_4016_ = v___x_3980_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4017_ = lean_box(0);
lean_inc(v_val_3964_);
v___x_4018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo_spec__1___redArg(v_constMap_4003_, v_val_3964_, v___x_4016_);
v___x_4019_ = lean_array_push(v_constOrder_4004_, v_val_3964_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 6, v___x_4019_);
lean_ctor_set(v___x_4006_, 5, v___x_4018_);
v___x_4021_ = v___x_4006_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_stream_3998_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_nameMap_3999_);
lean_ctor_set(v_reuseFailAlloc_4028_, 2, v_levelMap_4000_);
lean_ctor_set(v_reuseFailAlloc_4028_, 3, v_exprMap_4001_);
lean_ctor_set(v_reuseFailAlloc_4028_, 4, v_recursorRuleMap_4002_);
lean_ctor_set(v_reuseFailAlloc_4028_, 5, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4028_, 6, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4023_; 
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 1, v___x_4021_);
lean_ctor_set(v___x_3996_, 0, v___x_4017_);
v___x_4023_ = v___x_3996_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4025_; 
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v___x_4023_);
v___x_4025_ = v___x_3991_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_del_object(v___x_4006_);
lean_dec_ref(v_constOrder_4004_);
lean_dec_ref(v_constMap_4003_);
lean_dec_ref(v_recursorRuleMap_4002_);
lean_dec_ref(v_exprMap_4001_);
lean_dec_ref(v_levelMap_4000_);
lean_dec_ref(v_nameMap_3999_);
lean_dec_ref(v_stream_3998_);
lean_del_object(v___x_3996_);
lean_dec(v_fst_3994_);
lean_dec(v_fst_3984_);
lean_dec(v_val_3978_);
lean_dec(v_fst_3974_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
v___x_4030_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_addConst___closed__2));
v___x_4031_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3964_, v___x_4008_);
v___x_4032_ = lean_string_append(v___x_4030_, v___x_4031_);
lean_dec_ref(v___x_4031_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set_tag(v___x_3980_, 18);
lean_ctor_set(v___x_3980_, 0, v___x_4032_);
v___x_4034_ = v___x_3980_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4036_; 
if (v_isShared_3992_ == 0)
{
lean_ctor_set_tag(v___x_3991_, 1);
lean_ctor_set(v___x_3991_, 0, v___x_4034_);
v___x_4036_ = v___x_3991_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v_fst_3984_);
lean_del_object(v___x_3980_);
lean_dec(v_val_3978_);
lean_dec(v_fst_3974_);
lean_dec(v_val_3964_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
v_a_4042_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_3988_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_3988_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_del_object(v___x_3980_);
lean_dec(v_val_3978_);
lean_dec(v_fst_3974_);
lean_dec(v_val_3964_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
v_a_4050_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_3982_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_3982_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_dec(v___x_3977_);
lean_dec(v_fst_3974_);
lean_dec(v_snd_3973_);
lean_dec(v_val_3964_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
v___x_4059_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getExpr___closed__0));
v___x_4060_ = l_Nat_reprFast(v_a_3976_);
v___x_4061_ = lean_string_append(v___x_4059_, v___x_4060_);
lean_dec_ref(v___x_4060_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 18);
lean_ctor_set(v___x_3966_, 0, v___x_4061_);
v___x_4063_ = v___x_3966_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 1);
lean_ctor_set(v___x_3971_, 0, v___x_4063_);
v___x_4065_ = v___x_3971_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_del_object(v___x_3966_);
lean_dec(v_val_3964_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
v_a_4069_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_3968_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_3968_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4082_; 
lean_dec(v___x_3963_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec_ref(v_a_3849_);
v___x_4078_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_getName___closed__2));
v___x_4079_ = l_Nat_reprFast(v_a_3962_);
v___x_4080_ = lean_string_append(v___x_4078_, v___x_4079_);
lean_dec_ref(v___x_4079_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set_tag(v___x_3958_, 18);
lean_ctor_set(v___x_3958_, 0, v___x_4080_);
v___x_4082_ = v___x_3958_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set_tag(v___x_3952_, 1);
lean_ctor_set(v___x_3952_, 0, v___x_4082_);
v___x_4084_ = v___x_3952_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_del_object(v___x_3958_);
lean_dec(v_val_3956_);
lean_del_object(v___x_3952_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3881_;
}
}
}
else
{
lean_dec(v___x_3955_);
lean_del_object(v___x_3952_);
lean_dec_ref(v_elems_3950_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3881_;
}
}
}
else
{
lean_dec(v_val_3949_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3878_;
}
}
else
{
lean_dec(v___x_3948_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3878_;
}
}
else
{
lean_dec(v_val_3945_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3875_;
}
}
else
{
lean_dec(v___x_3944_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3875_;
}
}
}
else
{
lean_dec(v_exponent_3940_);
lean_dec(v_mantissa_3939_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3872_;
}
}
else
{
lean_dec(v_val_3937_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3872_;
}
}
else
{
lean_dec(v___x_3936_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3872_;
}
}
}
else
{
lean_dec(v_exponent_3932_);
lean_dec(v_mantissa_3931_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3869_;
}
}
else
{
lean_dec(v_val_3929_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3869_;
}
}
else
{
lean_dec(v___x_3928_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3869_;
}
}
}
else
{
lean_dec(v_exponent_3924_);
lean_dec(v_mantissa_3923_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3866_;
}
}
else
{
lean_dec(v_val_3921_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3866_;
}
}
else
{
lean_dec(v___x_3920_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3866_;
}
}
}
else
{
lean_dec(v_exponent_3916_);
lean_dec(v_mantissa_3915_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3863_;
}
}
else
{
lean_dec(v_val_3913_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3863_;
}
}
else
{
lean_dec(v___x_3912_);
lean_dec_ref(v_elems_3910_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3863_;
}
}
else
{
lean_dec(v_val_3909_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3860_;
}
}
else
{
lean_dec(v___x_3908_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3860_;
}
}
}
else
{
lean_dec(v_exponent_3904_);
lean_dec(v_mantissa_3903_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3857_;
}
}
else
{
lean_dec(v_val_3901_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3857_;
}
}
else
{
lean_dec(v___x_3900_);
lean_dec_ref(v_elems_3898_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3857_;
}
}
else
{
lean_dec(v_val_3897_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3854_;
}
}
else
{
lean_dec(v___x_3896_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3854_;
}
}
}
else
{
lean_dec(v_exponent_3890_);
lean_dec(v_mantissa_3889_);
lean_dec_ref(v_a_3849_);
goto v___jp_3851_;
}
}
else
{
lean_dec(v_val_3887_);
lean_dec_ref(v_a_3849_);
goto v___jp_3851_;
}
}
else
{
lean_dec(v___x_3886_);
lean_dec_ref(v_a_3849_);
goto v___jp_3851_;
}
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v_a_3849_);
v___x_4089_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
v___jp_3851_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
return v___x_3853_;
}
v___jp_3854_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
return v___x_3856_;
}
v___jp_3857_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
return v___x_3859_;
}
v___jp_3860_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
v___jp_3863_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
v___jp_3866_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
v___jp_3869_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
v___jp_3872_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
return v___x_3874_;
}
v___jp_3875_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
return v___x_3877_;
}
v___jp_3878_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
return v___x_3880_;
}
v___jp_3881_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_List_mapM_loop___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo_spec__0___closed__1));
v___x_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo___boxed(lean_object* v_json_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v_json_4091_, v_a_4092_);
lean_dec(v_json_4091_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(lean_object* v_as_4095_, size_t v_i_4096_, size_t v_stop_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_){
_start:
{
uint8_t v___x_4101_; 
v___x_4101_ = lean_usize_dec_eq(v_i_4096_, v_stop_4097_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = lean_array_uget_borrowed(v_as_4095_, v_i_4096_);
v___x_4103_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseRecInfo(v___x_4102_, v___y_4099_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v_fst_4105_; lean_object* v_snd_4106_; size_t v___x_4107_; size_t v___x_4108_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v_fst_4105_ = lean_ctor_get(v_a_4104_, 0);
lean_inc(v_fst_4105_);
v_snd_4106_ = lean_ctor_get(v_a_4104_, 1);
lean_inc(v_snd_4106_);
lean_dec(v_a_4104_);
v___x_4107_ = ((size_t)1ULL);
v___x_4108_ = lean_usize_add(v_i_4096_, v___x_4107_);
v_i_4096_ = v___x_4108_;
v_b_4098_ = v_fst_4105_;
v___y_4099_ = v_snd_4106_;
goto _start;
}
else
{
return v___x_4103_;
}
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_b_4098_);
lean_ctor_set(v___x_4110_, 1, v___y_4099_);
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0___boxed(lean_object* v_as_4112_, lean_object* v_i_4113_, lean_object* v_stop_4114_, lean_object* v_b_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
size_t v_i_boxed_4118_; size_t v_stop_boxed_4119_; lean_object* v_res_4120_; 
v_i_boxed_4118_ = lean_unbox_usize(v_i_4113_);
lean_dec(v_i_4113_);
v_stop_boxed_4119_ = lean_unbox_usize(v_stop_4114_);
lean_dec(v_stop_4114_);
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_as_4112_, v_i_boxed_4118_, v_stop_boxed_4119_, v_b_4115_, v___y_4116_);
lean_dec_ref(v_as_4112_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(lean_object* v_as_4121_, size_t v_i_4122_, size_t v_stop_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_usize_dec_eq(v_i_4122_, v_stop_4123_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_array_uget_borrowed(v_as_4121_, v_i_4122_);
v___x_4129_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseCtorInfo(v___x_4128_, v___y_4125_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v_fst_4131_; lean_object* v_snd_4132_; size_t v___x_4133_; size_t v___x_4134_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v_fst_4131_ = lean_ctor_get(v_a_4130_, 0);
lean_inc(v_fst_4131_);
v_snd_4132_ = lean_ctor_get(v_a_4130_, 1);
lean_inc(v_snd_4132_);
lean_dec(v_a_4130_);
v___x_4133_ = ((size_t)1ULL);
v___x_4134_ = lean_usize_add(v_i_4122_, v___x_4133_);
v_i_4122_ = v___x_4134_;
v_b_4124_ = v_fst_4131_;
v___y_4125_ = v_snd_4132_;
goto _start;
}
else
{
return v___x_4129_;
}
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v_b_4124_);
lean_ctor_set(v___x_4136_, 1, v___y_4125_);
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1___boxed(lean_object* v_as_4138_, lean_object* v_i_4139_, lean_object* v_stop_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
size_t v_i_boxed_4144_; size_t v_stop_boxed_4145_; lean_object* v_res_4146_; 
v_i_boxed_4144_ = lean_unbox_usize(v_i_4139_);
lean_dec(v_i_4139_);
v_stop_boxed_4145_ = lean_unbox_usize(v_stop_4140_);
lean_dec(v_stop_4140_);
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_as_4138_, v_i_boxed_4144_, v_stop_boxed_4145_, v_b_4141_, v___y_4142_);
lean_dec_ref(v_as_4138_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(lean_object* v_as_4147_, size_t v_i_4148_, size_t v_stop_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_){
_start:
{
uint8_t v___x_4153_; 
v___x_4153_ = lean_usize_dec_eq(v_i_4148_, v_stop_4149_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_array_uget_borrowed(v_as_4147_, v_i_4148_);
v___x_4155_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo(v___x_4154_, v___y_4151_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v_fst_4157_; lean_object* v_snd_4158_; size_t v___x_4159_; size_t v___x_4160_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v_fst_4157_ = lean_ctor_get(v_a_4156_, 0);
lean_inc(v_fst_4157_);
v_snd_4158_ = lean_ctor_get(v_a_4156_, 1);
lean_inc(v_snd_4158_);
lean_dec(v_a_4156_);
v___x_4159_ = ((size_t)1ULL);
v___x_4160_ = lean_usize_add(v_i_4148_, v___x_4159_);
v_i_4148_ = v___x_4160_;
v_b_4150_ = v_fst_4157_;
v___y_4151_ = v_snd_4158_;
goto _start;
}
else
{
return v___x_4155_;
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v_b_4150_);
lean_ctor_set(v___x_4162_, 1, v___y_4151_);
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2___boxed(lean_object* v_as_4164_, lean_object* v_i_4165_, lean_object* v_stop_4166_, lean_object* v_b_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
size_t v_i_boxed_4170_; size_t v_stop_boxed_4171_; lean_object* v_res_4172_; 
v_i_boxed_4170_ = lean_unbox_usize(v_i_4165_);
lean_dec(v_i_4165_);
v_stop_boxed_4171_ = lean_unbox_usize(v_stop_4166_);
lean_dec(v_stop_4166_);
v_res_4172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_as_4164_, v_i_boxed_4170_, v_stop_boxed_4171_, v_b_4167_, v___y_4168_);
lean_dec_ref(v_as_4164_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(lean_object* v_data_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__6));
v___x_4197_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4184_, v___x_4196_);
if (lean_obj_tag(v___x_4197_) == 1)
{
lean_object* v_val_4198_; 
v_val_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_val_4198_);
lean_dec_ref_known(v___x_4197_, 1);
if (lean_obj_tag(v_val_4198_) == 4)
{
lean_object* v_elems_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_elems_4199_ = lean_ctor_get(v_val_4198_, 0);
lean_inc_ref(v_elems_4199_);
lean_dec_ref_known(v_val_4198_, 1);
v___x_4200_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductInfo___closed__4));
v___x_4201_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4184_, v___x_4200_);
if (lean_obj_tag(v___x_4201_) == 1)
{
lean_object* v_val_4202_; 
v_val_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_val_4202_);
lean_dec_ref_known(v___x_4201_, 1);
if (lean_obj_tag(v_val_4202_) == 4)
{
lean_object* v_elems_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_elems_4203_ = lean_ctor_get(v_val_4202_, 0);
lean_inc_ref(v_elems_4203_);
lean_dec_ref_known(v_val_4202_, 1);
v___x_4204_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__7));
v___x_4205_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr_spec__0___redArg(v_data_4184_, v___x_4204_);
if (lean_obj_tag(v___x_4205_) == 1)
{
lean_object* v_val_4206_; 
v_val_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_val_4206_);
lean_dec_ref_known(v___x_4205_, 1);
if (lean_obj_tag(v_val_4206_) == 4)
{
lean_object* v_elems_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4262_; 
v_elems_4207_ = lean_ctor_get(v_val_4206_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_val_4206_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4209_ = v_val_4206_;
v_isShared_4210_ = v_isSharedCheck_4262_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_elems_4207_);
lean_dec(v_val_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4262_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; lean_object* v_snd_4213_; lean_object* v___y_4233_; lean_object* v_snd_4237_; lean_object* v___y_4249_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_array_get_size(v_elems_4199_);
v___x_4253_ = lean_nat_dec_lt(v___x_4211_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_dec_ref(v_elems_4199_);
v_snd_4237_ = v_a_4185_;
goto v___jp_4236_;
}
else
{
lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4254_ = lean_box(0);
v___x_4255_ = lean_nat_dec_le(v___x_4252_, v___x_4252_);
if (v___x_4255_ == 0)
{
if (v___x_4253_ == 0)
{
lean_dec_ref(v_elems_4199_);
v_snd_4237_ = v_a_4185_;
goto v___jp_4236_;
}
else
{
size_t v___x_4256_; size_t v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = ((size_t)0ULL);
v___x_4257_ = lean_usize_of_nat(v___x_4252_);
v___x_4258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4199_, v___x_4256_, v___x_4257_, v___x_4254_, v_a_4185_);
lean_dec_ref(v_elems_4199_);
v___y_4249_ = v___x_4258_;
goto v___jp_4248_;
}
}
else
{
size_t v___x_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = ((size_t)0ULL);
v___x_4260_ = lean_usize_of_nat(v___x_4252_);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__2(v_elems_4199_, v___x_4259_, v___x_4260_, v___x_4254_, v_a_4185_);
lean_dec_ref(v_elems_4199_);
v___y_4249_ = v___x_4261_;
goto v___jp_4248_;
}
}
v___jp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4214_ = lean_array_get_size(v_elems_4207_);
v___x_4215_ = lean_box(0);
v___x_4216_ = lean_nat_dec_lt(v___x_4211_, v___x_4214_);
if (v___x_4216_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
lean_dec_ref(v_elems_4207_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v_snd_4213_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
else
{
uint8_t v___x_4221_; 
v___x_4221_ = lean_nat_dec_le(v___x_4214_, v___x_4214_);
if (v___x_4221_ == 0)
{
if (v___x_4216_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
lean_dec_ref(v_elems_4207_);
v___x_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4215_);
lean_ctor_set(v___x_4222_, 1, v_snd_4213_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4222_);
v___x_4224_ = v___x_4209_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
else
{
size_t v___x_4226_; size_t v___x_4227_; lean_object* v___x_4228_; 
lean_del_object(v___x_4209_);
v___x_4226_ = ((size_t)0ULL);
v___x_4227_ = lean_usize_of_nat(v___x_4214_);
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4207_, v___x_4226_, v___x_4227_, v___x_4215_, v_snd_4213_);
lean_dec_ref(v_elems_4207_);
return v___x_4228_;
}
}
else
{
size_t v___x_4229_; size_t v___x_4230_; lean_object* v___x_4231_; 
lean_del_object(v___x_4209_);
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = lean_usize_of_nat(v___x_4214_);
v___x_4231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__0(v_elems_4207_, v___x_4229_, v___x_4230_, v___x_4215_, v_snd_4213_);
lean_dec_ref(v_elems_4207_);
return v___x_4231_;
}
}
}
v___jp_4232_:
{
if (lean_obj_tag(v___y_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v_snd_4235_; 
v_a_4234_ = lean_ctor_get(v___y_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___y_4233_, 1);
v_snd_4235_ = lean_ctor_get(v_a_4234_, 1);
lean_inc(v_snd_4235_);
lean_dec(v_a_4234_);
v_snd_4213_ = v_snd_4235_;
goto v___jp_4212_;
}
else
{
lean_del_object(v___x_4209_);
lean_dec_ref(v_elems_4207_);
return v___y_4233_;
}
}
v___jp_4236_:
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_array_get_size(v_elems_4203_);
v___x_4239_ = lean_nat_dec_lt(v___x_4211_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_dec_ref(v_elems_4203_);
v_snd_4213_ = v_snd_4237_;
goto v___jp_4212_;
}
else
{
lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4240_ = lean_box(0);
v___x_4241_ = lean_nat_dec_le(v___x_4238_, v___x_4238_);
if (v___x_4241_ == 0)
{
if (v___x_4239_ == 0)
{
lean_dec_ref(v_elems_4203_);
v_snd_4213_ = v_snd_4237_;
goto v___jp_4212_;
}
else
{
size_t v___x_4242_; size_t v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = ((size_t)0ULL);
v___x_4243_ = lean_usize_of_nat(v___x_4238_);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4203_, v___x_4242_, v___x_4243_, v___x_4240_, v_snd_4237_);
lean_dec_ref(v_elems_4203_);
v___y_4233_ = v___x_4244_;
goto v___jp_4232_;
}
}
else
{
size_t v___x_4245_; size_t v___x_4246_; lean_object* v___x_4247_; 
v___x_4245_ = ((size_t)0ULL);
v___x_4246_ = lean_usize_of_nat(v___x_4238_);
v___x_4247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseInductive_spec__1(v_elems_4203_, v___x_4245_, v___x_4246_, v___x_4240_, v_snd_4237_);
lean_dec_ref(v_elems_4203_);
v___y_4233_ = v___x_4247_;
goto v___jp_4232_;
}
}
}
v___jp_4248_:
{
if (lean_obj_tag(v___y_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v_snd_4251_; 
v_a_4250_ = lean_ctor_get(v___y_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref_known(v___y_4249_, 1);
v_snd_4251_ = lean_ctor_get(v_a_4250_, 1);
lean_inc(v_snd_4251_);
lean_dec(v_a_4250_);
v_snd_4237_ = v_snd_4251_;
goto v___jp_4236_;
}
else
{
lean_del_object(v___x_4209_);
lean_dec_ref(v_elems_4207_);
lean_dec_ref(v_elems_4203_);
return v___y_4249_;
}
}
}
}
else
{
lean_dec(v_val_4206_);
lean_dec_ref(v_elems_4203_);
lean_dec_ref(v_elems_4199_);
lean_dec_ref(v_a_4185_);
goto v___jp_4187_;
}
}
else
{
lean_dec(v___x_4205_);
lean_dec_ref(v_elems_4203_);
lean_dec_ref(v_elems_4199_);
lean_dec_ref(v_a_4185_);
goto v___jp_4187_;
}
}
else
{
lean_dec(v_val_4202_);
lean_dec_ref(v_elems_4199_);
lean_dec_ref(v_a_4185_);
goto v___jp_4190_;
}
}
else
{
lean_dec(v___x_4201_);
lean_dec_ref(v_elems_4199_);
lean_dec_ref(v_a_4185_);
goto v___jp_4190_;
}
}
else
{
lean_dec(v_val_4198_);
lean_dec_ref(v_a_4185_);
goto v___jp_4193_;
}
}
else
{
lean_dec(v___x_4197_);
lean_dec_ref(v_a_4185_);
goto v___jp_4193_;
}
v___jp_4187_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__1));
v___x_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
return v___x_4189_;
}
v___jp_4190_:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__3));
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
v___jp_4193_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___closed__5));
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive___boxed(lean_object* v_data_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_data_4263_, v_a_4264_);
lean_dec(v_data_4263_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(lean_object* v_x_4268_, lean_object* v_x_4269_){
_start:
{
if (lean_obj_tag(v_x_4269_) == 0)
{
return v_x_4268_;
}
else
{
lean_object* v_head_4270_; lean_object* v_tail_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_head_4270_ = lean_ctor_get(v_x_4269_, 0);
v_tail_4271_ = lean_ctor_get(v_x_4269_, 1);
v___x_4272_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___closed__0));
v___x_4273_ = lean_string_append(v_x_4268_, v___x_4272_);
v___x_4274_ = lean_string_append(v___x_4273_, v_head_4270_);
v_x_4268_ = v___x_4274_;
v_x_4269_ = v_tail_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1___boxed(lean_object* v_x_4276_, lean_object* v_x_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v_x_4276_, v_x_4277_);
lean_dec(v_x_4277_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(lean_object* v_x_4282_){
_start:
{
if (lean_obj_tag(v_x_4282_) == 0)
{
lean_object* v___x_4283_; 
v___x_4283_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__0));
return v___x_4283_;
}
else
{
lean_object* v_tail_4284_; 
v_tail_4284_ = lean_ctor_get(v_x_4282_, 1);
if (lean_obj_tag(v_tail_4284_) == 0)
{
lean_object* v_head_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_head_4285_ = lean_ctor_get(v_x_4282_, 0);
v___x_4286_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4287_ = lean_string_append(v___x_4286_, v_head_4285_);
v___x_4288_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__2));
v___x_4289_ = lean_string_append(v___x_4287_, v___x_4288_);
return v___x_4289_;
}
else
{
lean_object* v_head_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; uint32_t v___x_4294_; lean_object* v___x_4295_; 
v_head_4290_ = lean_ctor_get(v_x_4282_, 0);
v___x_4291_ = ((lean_object*)(l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___closed__1));
v___x_4292_ = lean_string_append(v___x_4291_, v_head_4290_);
v___x_4293_ = l_List_foldl___at___00List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1_spec__1(v___x_4292_, v_tail_4284_);
v___x_4294_ = 93;
v___x_4295_ = lean_string_push(v___x_4293_, v___x_4294_);
return v___x_4295_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1___boxed(lean_object* v_x_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v_x_4296_);
lean_dec(v_x_4296_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(lean_object* v_init_4298_, lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 0)
{
lean_object* v_k_4300_; lean_object* v_v_4301_; lean_object* v_l_4302_; lean_object* v_r_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_k_4300_ = lean_ctor_get(v_x_4299_, 1);
v_v_4301_ = lean_ctor_get(v_x_4299_, 2);
v_l_4302_ = lean_ctor_get(v_x_4299_, 3);
v_r_4303_ = lean_ctor_get(v_x_4299_, 4);
v___x_4304_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_init_4298_, v_r_4303_);
lean_inc(v_v_4301_);
lean_inc(v_k_4300_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_k_4300_);
lean_ctor_set(v___x_4305_, 1, v_v_4301_);
v___x_4306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___x_4304_);
v_init_4298_ = v___x_4306_;
v_x_4299_ = v_l_4302_;
goto _start;
}
else
{
return v_init_4298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2___boxed(lean_object* v_init_4308_, lean_object* v_x_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v_init_4308_, v_x_4309_);
lean_dec(v_x_4309_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(lean_object* v_init_4311_, lean_object* v_x_4312_){
_start:
{
if (lean_obj_tag(v_x_4312_) == 0)
{
lean_object* v_k_4313_; lean_object* v_l_4314_; lean_object* v_r_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_k_4313_ = lean_ctor_get(v_x_4312_, 1);
v_l_4314_ = lean_ctor_get(v_x_4312_, 3);
v_r_4315_ = lean_ctor_get(v_x_4312_, 4);
v___x_4316_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4311_, v_r_4315_);
lean_inc(v_k_4313_);
v___x_4317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4317_, 0, v_k_4313_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v_init_4311_ = v___x_4317_;
v_x_4312_ = v_l_4314_;
goto _start;
}
else
{
return v_init_4311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0___boxed(lean_object* v_init_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v_init_4319_, v_x_4320_);
lean_dec(v_x_4320_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(lean_object* v_line_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4353_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__2));
v___x_4354_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_4353_, v_line_4347_);
if (lean_obj_tag(v___x_4354_) == 1)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_5228_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_5228_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_5228_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
if (lean_obj_tag(v_a_4355_) == 5)
{
lean_object* v_kvPairs_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_5227_; 
v_kvPairs_4359_ = lean_ctor_get(v_a_4355_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v_a_4355_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_4361_ = v_a_4355_;
v_isShared_4362_ = v_isSharedCheck_5227_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_kvPairs_4359_);
lean_dec(v_a_4355_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_5227_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_fst_4376_; lean_object* v_snd_4377_; lean_object* v_tail_4378_; lean_object* v___y_5194_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5199_ = lean_box(0);
v___x_5200_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__2(v___x_5199_, v_kvPairs_4359_);
if (lean_obj_tag(v___x_5200_) == 1)
{
lean_object* v_tail_5201_; 
v_tail_5201_ = lean_ctor_get(v___x_5200_, 1);
lean_inc(v_tail_5201_);
if (lean_obj_tag(v_tail_5201_) == 1)
{
lean_object* v_head_5202_; lean_object* v_head_5203_; lean_object* v_tail_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5225_; 
v_head_5202_ = lean_ctor_get(v_tail_5201_, 0);
lean_inc(v_head_5202_);
v_head_5203_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_head_5203_);
v_tail_5204_ = lean_ctor_get(v_tail_5201_, 1);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_tail_5201_);
if (v_isSharedCheck_5225_ == 0)
{
lean_object* v_unused_5226_; 
v_unused_5226_ = lean_ctor_get(v_tail_5201_, 0);
lean_dec(v_unused_5226_);
v___x_5206_ = v_tail_5201_;
v_isShared_5207_ = v_isSharedCheck_5225_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_tail_5204_);
lean_dec(v_tail_5201_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5225_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v_fst_5208_; lean_object* v_snd_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; 
v_fst_5208_ = lean_ctor_get(v_head_5202_, 0);
lean_inc(v_fst_5208_);
v_snd_5209_ = lean_ctor_get(v_head_5202_, 1);
lean_inc(v_snd_5209_);
lean_dec(v_head_5202_);
v___x_5210_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_5211_ = lean_string_dec_eq(v_fst_5208_, v___x_5210_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; uint8_t v___x_5213_; 
v___x_5212_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_5213_ = lean_string_dec_eq(v_fst_5208_, v___x_5212_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5214_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_5215_ = lean_string_dec_eq(v_fst_5208_, v___x_5214_);
lean_dec(v_fst_5208_);
if (v___x_5215_ == 0)
{
lean_dec(v_snd_5209_);
lean_del_object(v___x_5206_);
lean_dec(v_tail_5204_);
lean_dec(v_head_5203_);
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
else
{
if (lean_obj_tag(v_tail_5204_) == 0)
{
lean_object* v___x_5217_; 
lean_dec_ref_known(v___x_5200_, 2);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_head_5203_);
v___x_5217_ = v___x_5206_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_head_5203_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_tail_5204_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
v_fst_4376_ = v___x_5214_;
v_snd_4377_ = v_snd_5209_;
v_tail_4378_ = v___x_5217_;
goto v___jp_4375_;
}
}
else
{
lean_dec(v_snd_5209_);
lean_del_object(v___x_5206_);
lean_dec(v_tail_5204_);
lean_dec(v_head_5203_);
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
}
}
else
{
lean_dec(v_fst_5208_);
if (lean_obj_tag(v_tail_5204_) == 0)
{
lean_object* v___x_5220_; 
lean_dec_ref_known(v___x_5200_, 2);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_head_5203_);
v___x_5220_ = v___x_5206_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_head_5203_);
lean_ctor_set(v_reuseFailAlloc_5221_, 1, v_tail_5204_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
v_fst_4376_ = v___x_5212_;
v_snd_4377_ = v_snd_5209_;
v_tail_4378_ = v___x_5220_;
goto v___jp_4375_;
}
}
else
{
lean_dec(v_snd_5209_);
lean_del_object(v___x_5206_);
lean_dec(v_tail_5204_);
lean_dec(v_head_5203_);
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
}
}
else
{
lean_dec(v_fst_5208_);
if (lean_obj_tag(v_tail_5204_) == 0)
{
lean_object* v___x_5223_; 
lean_dec_ref_known(v___x_5200_, 2);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_head_5203_);
v___x_5223_ = v___x_5206_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_head_5203_);
lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_tail_5204_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
v_fst_4376_ = v___x_5210_;
v_snd_4377_ = v_snd_5209_;
v_tail_4378_ = v___x_5223_;
goto v___jp_4375_;
}
}
else
{
lean_dec(v_snd_5209_);
lean_del_object(v___x_5206_);
lean_dec(v_tail_5204_);
lean_dec(v_head_5203_);
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
}
}
}
else
{
lean_dec(v_tail_5201_);
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
}
else
{
v___y_5194_ = v___x_5200_;
goto v___jp_5193_;
}
v___jp_4363_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4364_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__0));
v___x_4365_ = lean_box(0);
v___x_4366_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__0(v___x_4365_, v_kvPairs_4359_);
lean_dec(v_kvPairs_4359_);
v___x_4367_ = l_List_toString___at___00__private_LeanExport_Parse_0__LeanExport_Parse_parseItem_spec__1(v___x_4366_);
lean_dec(v___x_4366_);
v___x_4368_ = lean_string_append(v___x_4364_, v___x_4367_);
lean_dec_ref(v___x_4367_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set_tag(v___x_4361_, 18);
lean_ctor_set(v___x_4361_, 0, v___x_4368_);
v___x_4370_ = v___x_4361_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
lean_object* v___x_4372_; 
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4370_);
v___x_4372_ = v___x_4357_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
v___jp_4375_:
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__1));
v___x_4380_ = lean_string_dec_eq(v_fst_4376_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__2));
v___x_4382_ = lean_string_dec_eq(v_fst_4376_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__3));
v___x_4384_ = lean_string_dec_eq(v_fst_4376_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4385_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__4));
v___x_4386_ = lean_string_dec_eq(v_fst_4376_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__5));
v___x_4388_ = lean_string_dec_eq(v_fst_4376_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__6));
v___x_4390_ = lean_string_dec_eq(v_fst_4376_, v___x_4389_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4391_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo___closed__9));
v___x_4392_ = lean_string_dec_eq(v_fst_4376_, v___x_4391_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4393_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__7));
v___x_4394_ = lean_string_dec_eq(v_fst_4376_, v___x_4393_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__8));
v___x_4396_ = lean_string_dec_eq(v_fst_4376_, v___x_4395_);
lean_dec_ref(v_fst_4376_);
if (v___x_4396_ == 0)
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4397_; lean_object* v___x_4398_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4397_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4397_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4398_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseInductive(v_kvPairs_4397_, v_a_4348_);
lean_dec(v_kvPairs_4397_);
return v___x_4398_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4399_; lean_object* v___x_4400_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4399_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4399_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4400_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseQuotInfo(v_kvPairs_4399_, v_a_4348_);
lean_dec(v_kvPairs_4399_);
return v___x_4400_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4401_; lean_object* v___x_4402_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4401_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4401_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4402_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseOpaqueInfo(v_kvPairs_4401_, v_a_4348_);
lean_dec(v_kvPairs_4401_);
return v___x_4402_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4403_; lean_object* v___x_4404_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4403_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4403_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4404_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseThmInfo(v_kvPairs_4403_, v_a_4348_);
lean_dec(v_kvPairs_4403_);
return v___x_4404_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4405_; lean_object* v___x_4406_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4405_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4405_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4406_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseDefnInfo(v_kvPairs_4405_, v_a_4348_);
lean_dec(v_kvPairs_4405_);
return v___x_4406_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 5)
{
if (lean_obj_tag(v_tail_4378_) == 0)
{
lean_object* v_kvPairs_4407_; lean_object* v___x_4408_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v_kvPairs_4407_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc(v_kvPairs_4407_);
lean_dec_ref_known(v_snd_4377_, 1);
v___x_4408_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseAxiomInfo(v_kvPairs_4407_, v_a_4348_);
lean_dec(v_kvPairs_4407_);
return v___x_4408_;
}
else
{
lean_dec_ref_known(v_snd_4377_, 1);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 2)
{
lean_object* v_n_4409_; lean_object* v_mantissa_4410_; lean_object* v_exponent_4411_; lean_object* v_natZero_4412_; lean_object* v_intZero_4413_; uint8_t v_isNeg_4414_; 
v_n_4409_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc_ref(v_n_4409_);
lean_dec_ref_known(v_snd_4377_, 1);
v_mantissa_4410_ = lean_ctor_get(v_n_4409_, 0);
lean_inc(v_mantissa_4410_);
v_exponent_4411_ = lean_ctor_get(v_n_4409_, 1);
lean_inc(v_exponent_4411_);
lean_dec_ref(v_n_4409_);
v_natZero_4412_ = lean_unsigned_to_nat(0u);
v_intZero_4413_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4414_ = lean_int_dec_lt(v_mantissa_4410_, v_intZero_4413_);
if (v_isNeg_4414_ == 0)
{
uint8_t v___x_4415_; 
v___x_4415_ = lean_nat_dec_eq(v_exponent_4411_, v_natZero_4412_);
lean_dec(v_exponent_4411_);
if (v___x_4415_ == 0)
{
lean_dec(v_mantissa_4410_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_4378_) == 1)
{
lean_object* v_head_4416_; lean_object* v_tail_4417_; lean_object* v_fst_4418_; lean_object* v_snd_4419_; lean_object* v_a_4420_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v_head_4416_ = lean_ctor_get(v_tail_4378_, 0);
lean_inc(v_head_4416_);
v_tail_4417_ = lean_ctor_get(v_tail_4378_, 1);
lean_inc(v_tail_4417_);
lean_dec_ref_known(v_tail_4378_, 2);
v_fst_4418_ = lean_ctor_get(v_head_4416_, 0);
lean_inc(v_fst_4418_);
v_snd_4419_ = lean_ctor_get(v_head_4416_, 1);
lean_inc(v_snd_4419_);
lean_dec(v_head_4416_);
v_a_4420_ = lean_nat_abs(v_mantissa_4410_);
lean_dec(v_mantissa_4410_);
v___x_4421_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__9));
v___x_4422_ = lean_string_dec_eq(v_fst_4418_, v___x_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; uint8_t v___x_4424_; 
v___x_4423_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__10));
v___x_4424_ = lean_string_dec_eq(v_fst_4418_, v___x_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4425_; uint8_t v___x_4426_; 
v___x_4425_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__11));
v___x_4426_ = lean_string_dec_eq(v_fst_4418_, v___x_4425_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__12));
v___x_4428_ = lean_string_dec_eq(v_fst_4418_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; uint8_t v___x_4430_; 
v___x_4429_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__13));
v___x_4430_ = lean_string_dec_eq(v_fst_4418_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__14));
v___x_4432_ = lean_string_dec_eq(v_fst_4418_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__15));
v___x_4434_ = lean_string_dec_eq(v_fst_4418_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4435_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__16));
v___x_4436_ = lean_string_dec_eq(v_fst_4418_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__17));
v___x_4438_ = lean_string_dec_eq(v_fst_4418_, v___x_4437_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; uint8_t v___x_4440_; 
v___x_4439_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__18));
v___x_4440_ = lean_string_dec_eq(v_fst_4418_, v___x_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4441_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__19));
v___x_4442_ = lean_string_dec_eq(v_fst_4418_, v___x_4441_);
lean_dec(v_fst_4418_);
if (v___x_4442_ == 0)
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4443_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4443_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprMdata(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4476_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4446_ = v___x_4443_;
v_isShared_4447_ = v_isSharedCheck_4476_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4443_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4476_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v_snd_4448_; lean_object* v_fst_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4475_; 
v_snd_4448_ = lean_ctor_get(v_a_4444_, 1);
v_fst_4449_ = lean_ctor_get(v_a_4444_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_a_4444_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4451_ = v_a_4444_;
v_isShared_4452_ = v_isSharedCheck_4475_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_snd_4448_);
lean_inc(v_fst_4449_);
lean_dec(v_a_4444_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4475_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v_stream_4453_; lean_object* v_nameMap_4454_; lean_object* v_levelMap_4455_; lean_object* v_exprMap_4456_; lean_object* v_recursorRuleMap_4457_; lean_object* v_constMap_4458_; lean_object* v_constOrder_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4474_; 
v_stream_4453_ = lean_ctor_get(v_snd_4448_, 0);
v_nameMap_4454_ = lean_ctor_get(v_snd_4448_, 1);
v_levelMap_4455_ = lean_ctor_get(v_snd_4448_, 2);
v_exprMap_4456_ = lean_ctor_get(v_snd_4448_, 3);
v_recursorRuleMap_4457_ = lean_ctor_get(v_snd_4448_, 4);
v_constMap_4458_ = lean_ctor_get(v_snd_4448_, 5);
v_constOrder_4459_ = lean_ctor_get(v_snd_4448_, 6);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_snd_4448_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4461_ = v_snd_4448_;
v_isShared_4462_ = v_isSharedCheck_4474_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_constOrder_4459_);
lean_inc(v_constMap_4458_);
lean_inc(v_recursorRuleMap_4457_);
lean_inc(v_exprMap_4456_);
lean_inc(v_levelMap_4455_);
lean_inc(v_nameMap_4454_);
lean_inc(v_stream_4453_);
lean_dec(v_snd_4448_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4474_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4463_ = lean_box(0);
v___x_4464_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4456_, v_a_4420_, v_fst_4449_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 3, v___x_4464_);
v___x_4466_ = v___x_4461_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_stream_4453_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v_nameMap_4454_);
lean_ctor_set(v_reuseFailAlloc_4473_, 2, v_levelMap_4455_);
lean_ctor_set(v_reuseFailAlloc_4473_, 3, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4473_, 4, v_recursorRuleMap_4457_);
lean_ctor_set(v_reuseFailAlloc_4473_, 5, v_constMap_4458_);
lean_ctor_set(v_reuseFailAlloc_4473_, 6, v_constOrder_4459_);
v___x_4466_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4468_; 
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 1, v___x_4466_);
lean_ctor_set(v___x_4451_, 0, v___x_4463_);
v___x_4468_ = v___x_4451_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 0, v___x_4468_);
v___x_4470_ = v___x_4446_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec(v_a_4420_);
v_a_4477_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4443_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4443_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4485_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4485_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprStrLit(v_snd_4419_, v_a_4348_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4518_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4488_ = v___x_4485_;
v_isShared_4489_ = v_isSharedCheck_4518_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4518_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v_snd_4490_; lean_object* v_fst_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4517_; 
v_snd_4490_ = lean_ctor_get(v_a_4486_, 1);
v_fst_4491_ = lean_ctor_get(v_a_4486_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_a_4486_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4493_ = v_a_4486_;
v_isShared_4494_ = v_isSharedCheck_4517_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_snd_4490_);
lean_inc(v_fst_4491_);
lean_dec(v_a_4486_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4517_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v_stream_4495_; lean_object* v_nameMap_4496_; lean_object* v_levelMap_4497_; lean_object* v_exprMap_4498_; lean_object* v_recursorRuleMap_4499_; lean_object* v_constMap_4500_; lean_object* v_constOrder_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4516_; 
v_stream_4495_ = lean_ctor_get(v_snd_4490_, 0);
v_nameMap_4496_ = lean_ctor_get(v_snd_4490_, 1);
v_levelMap_4497_ = lean_ctor_get(v_snd_4490_, 2);
v_exprMap_4498_ = lean_ctor_get(v_snd_4490_, 3);
v_recursorRuleMap_4499_ = lean_ctor_get(v_snd_4490_, 4);
v_constMap_4500_ = lean_ctor_get(v_snd_4490_, 5);
v_constOrder_4501_ = lean_ctor_get(v_snd_4490_, 6);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_snd_4490_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4503_ = v_snd_4490_;
v_isShared_4504_ = v_isSharedCheck_4516_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_constOrder_4501_);
lean_inc(v_constMap_4500_);
lean_inc(v_recursorRuleMap_4499_);
lean_inc(v_exprMap_4498_);
lean_inc(v_levelMap_4497_);
lean_inc(v_nameMap_4496_);
lean_inc(v_stream_4495_);
lean_dec(v_snd_4490_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4516_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4505_ = lean_box(0);
v___x_4506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4498_, v_a_4420_, v_fst_4491_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 3, v___x_4506_);
v___x_4508_ = v___x_4503_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_stream_4495_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_nameMap_4496_);
lean_ctor_set(v_reuseFailAlloc_4515_, 2, v_levelMap_4497_);
lean_ctor_set(v_reuseFailAlloc_4515_, 3, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4515_, 4, v_recursorRuleMap_4499_);
lean_ctor_set(v_reuseFailAlloc_4515_, 5, v_constMap_4500_);
lean_ctor_set(v_reuseFailAlloc_4515_, 6, v_constOrder_4501_);
v___x_4508_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 1, v___x_4508_);
lean_ctor_set(v___x_4493_, 0, v___x_4505_);
v___x_4510_ = v___x_4493_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4510_);
v___x_4512_ = v___x_4488_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4420_);
v_a_4519_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4485_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4485_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4527_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4527_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprNatLit(v_snd_4419_, v_a_4348_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4560_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4560_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4560_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v_snd_4532_; lean_object* v_fst_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4559_; 
v_snd_4532_ = lean_ctor_get(v_a_4528_, 1);
v_fst_4533_ = lean_ctor_get(v_a_4528_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_a_4528_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4535_ = v_a_4528_;
v_isShared_4536_ = v_isSharedCheck_4559_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_snd_4532_);
lean_inc(v_fst_4533_);
lean_dec(v_a_4528_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4559_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v_stream_4537_; lean_object* v_nameMap_4538_; lean_object* v_levelMap_4539_; lean_object* v_exprMap_4540_; lean_object* v_recursorRuleMap_4541_; lean_object* v_constMap_4542_; lean_object* v_constOrder_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4558_; 
v_stream_4537_ = lean_ctor_get(v_snd_4532_, 0);
v_nameMap_4538_ = lean_ctor_get(v_snd_4532_, 1);
v_levelMap_4539_ = lean_ctor_get(v_snd_4532_, 2);
v_exprMap_4540_ = lean_ctor_get(v_snd_4532_, 3);
v_recursorRuleMap_4541_ = lean_ctor_get(v_snd_4532_, 4);
v_constMap_4542_ = lean_ctor_get(v_snd_4532_, 5);
v_constOrder_4543_ = lean_ctor_get(v_snd_4532_, 6);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_snd_4532_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4545_ = v_snd_4532_;
v_isShared_4546_ = v_isSharedCheck_4558_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_constOrder_4543_);
lean_inc(v_constMap_4542_);
lean_inc(v_recursorRuleMap_4541_);
lean_inc(v_exprMap_4540_);
lean_inc(v_levelMap_4539_);
lean_inc(v_nameMap_4538_);
lean_inc(v_stream_4537_);
lean_dec(v_snd_4532_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4558_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4547_ = lean_box(0);
v___x_4548_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4540_, v_a_4420_, v_fst_4533_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 3, v___x_4548_);
v___x_4550_ = v___x_4545_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_stream_4537_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_nameMap_4538_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_levelMap_4539_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_recursorRuleMap_4541_);
lean_ctor_set(v_reuseFailAlloc_4557_, 5, v_constMap_4542_);
lean_ctor_set(v_reuseFailAlloc_4557_, 6, v_constOrder_4543_);
v___x_4550_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4552_; 
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 1, v___x_4550_);
lean_ctor_set(v___x_4535_, 0, v___x_4547_);
v___x_4552_ = v___x_4535_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v___x_4550_);
v___x_4552_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4554_; 
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4552_);
v___x_4554_ = v___x_4530_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec(v_a_4420_);
v_a_4561_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4527_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4527_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4569_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4569_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprProj(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4602_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4602_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4602_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v_snd_4574_; lean_object* v_fst_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4601_; 
v_snd_4574_ = lean_ctor_get(v_a_4570_, 1);
v_fst_4575_ = lean_ctor_get(v_a_4570_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_a_4570_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4577_ = v_a_4570_;
v_isShared_4578_ = v_isSharedCheck_4601_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_snd_4574_);
lean_inc(v_fst_4575_);
lean_dec(v_a_4570_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4601_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v_stream_4579_; lean_object* v_nameMap_4580_; lean_object* v_levelMap_4581_; lean_object* v_exprMap_4582_; lean_object* v_recursorRuleMap_4583_; lean_object* v_constMap_4584_; lean_object* v_constOrder_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4600_; 
v_stream_4579_ = lean_ctor_get(v_snd_4574_, 0);
v_nameMap_4580_ = lean_ctor_get(v_snd_4574_, 1);
v_levelMap_4581_ = lean_ctor_get(v_snd_4574_, 2);
v_exprMap_4582_ = lean_ctor_get(v_snd_4574_, 3);
v_recursorRuleMap_4583_ = lean_ctor_get(v_snd_4574_, 4);
v_constMap_4584_ = lean_ctor_get(v_snd_4574_, 5);
v_constOrder_4585_ = lean_ctor_get(v_snd_4574_, 6);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_snd_4574_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4587_ = v_snd_4574_;
v_isShared_4588_ = v_isSharedCheck_4600_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_constOrder_4585_);
lean_inc(v_constMap_4584_);
lean_inc(v_recursorRuleMap_4583_);
lean_inc(v_exprMap_4582_);
lean_inc(v_levelMap_4581_);
lean_inc(v_nameMap_4580_);
lean_inc(v_stream_4579_);
lean_dec(v_snd_4574_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4600_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v___x_4589_ = lean_box(0);
v___x_4590_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4582_, v_a_4420_, v_fst_4575_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 3, v___x_4590_);
v___x_4592_ = v___x_4587_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_stream_4579_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v_nameMap_4580_);
lean_ctor_set(v_reuseFailAlloc_4599_, 2, v_levelMap_4581_);
lean_ctor_set(v_reuseFailAlloc_4599_, 3, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4599_, 4, v_recursorRuleMap_4583_);
lean_ctor_set(v_reuseFailAlloc_4599_, 5, v_constMap_4584_);
lean_ctor_set(v_reuseFailAlloc_4599_, 6, v_constOrder_4585_);
v___x_4592_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4594_; 
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 1, v___x_4592_);
lean_ctor_set(v___x_4577_, 0, v___x_4589_);
v___x_4594_ = v___x_4577_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4596_; 
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4594_);
v___x_4596_ = v___x_4572_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec(v_a_4420_);
v_a_4603_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4569_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4569_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4611_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4611_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLetE(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4644_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4644_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4644_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_snd_4616_; lean_object* v_fst_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4643_; 
v_snd_4616_ = lean_ctor_get(v_a_4612_, 1);
v_fst_4617_ = lean_ctor_get(v_a_4612_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_a_4612_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4619_ = v_a_4612_;
v_isShared_4620_ = v_isSharedCheck_4643_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_snd_4616_);
lean_inc(v_fst_4617_);
lean_dec(v_a_4612_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4643_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v_stream_4621_; lean_object* v_nameMap_4622_; lean_object* v_levelMap_4623_; lean_object* v_exprMap_4624_; lean_object* v_recursorRuleMap_4625_; lean_object* v_constMap_4626_; lean_object* v_constOrder_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4642_; 
v_stream_4621_ = lean_ctor_get(v_snd_4616_, 0);
v_nameMap_4622_ = lean_ctor_get(v_snd_4616_, 1);
v_levelMap_4623_ = lean_ctor_get(v_snd_4616_, 2);
v_exprMap_4624_ = lean_ctor_get(v_snd_4616_, 3);
v_recursorRuleMap_4625_ = lean_ctor_get(v_snd_4616_, 4);
v_constMap_4626_ = lean_ctor_get(v_snd_4616_, 5);
v_constOrder_4627_ = lean_ctor_get(v_snd_4616_, 6);
v_isSharedCheck_4642_ = !lean_is_exclusive(v_snd_4616_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4629_ = v_snd_4616_;
v_isShared_4630_ = v_isSharedCheck_4642_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_constOrder_4627_);
lean_inc(v_constMap_4626_);
lean_inc(v_recursorRuleMap_4625_);
lean_inc(v_exprMap_4624_);
lean_inc(v_levelMap_4623_);
lean_inc(v_nameMap_4622_);
lean_inc(v_stream_4621_);
lean_dec(v_snd_4616_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4642_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4631_ = lean_box(0);
v___x_4632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4624_, v_a_4420_, v_fst_4617_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 3, v___x_4632_);
v___x_4634_ = v___x_4629_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_stream_4621_);
lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_nameMap_4622_);
lean_ctor_set(v_reuseFailAlloc_4641_, 2, v_levelMap_4623_);
lean_ctor_set(v_reuseFailAlloc_4641_, 3, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4641_, 4, v_recursorRuleMap_4625_);
lean_ctor_set(v_reuseFailAlloc_4641_, 5, v_constMap_4626_);
lean_ctor_set(v_reuseFailAlloc_4641_, 6, v_constOrder_4627_);
v___x_4634_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4636_; 
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v___x_4634_);
lean_ctor_set(v___x_4619_, 0, v___x_4631_);
v___x_4636_ = v___x_4619_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4638_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4636_);
v___x_4638_ = v___x_4614_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_dec(v_a_4420_);
v_a_4645_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4611_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4611_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4653_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4653_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprForallE(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4686_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4656_ = v___x_4653_;
v_isShared_4657_ = v_isSharedCheck_4686_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4653_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4686_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v_snd_4658_; lean_object* v_fst_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4685_; 
v_snd_4658_ = lean_ctor_get(v_a_4654_, 1);
v_fst_4659_ = lean_ctor_get(v_a_4654_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_a_4654_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4661_ = v_a_4654_;
v_isShared_4662_ = v_isSharedCheck_4685_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_snd_4658_);
lean_inc(v_fst_4659_);
lean_dec(v_a_4654_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4685_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v_stream_4663_; lean_object* v_nameMap_4664_; lean_object* v_levelMap_4665_; lean_object* v_exprMap_4666_; lean_object* v_recursorRuleMap_4667_; lean_object* v_constMap_4668_; lean_object* v_constOrder_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4684_; 
v_stream_4663_ = lean_ctor_get(v_snd_4658_, 0);
v_nameMap_4664_ = lean_ctor_get(v_snd_4658_, 1);
v_levelMap_4665_ = lean_ctor_get(v_snd_4658_, 2);
v_exprMap_4666_ = lean_ctor_get(v_snd_4658_, 3);
v_recursorRuleMap_4667_ = lean_ctor_get(v_snd_4658_, 4);
v_constMap_4668_ = lean_ctor_get(v_snd_4658_, 5);
v_constOrder_4669_ = lean_ctor_get(v_snd_4658_, 6);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_snd_4658_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4671_ = v_snd_4658_;
v_isShared_4672_ = v_isSharedCheck_4684_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_constOrder_4669_);
lean_inc(v_constMap_4668_);
lean_inc(v_recursorRuleMap_4667_);
lean_inc(v_exprMap_4666_);
lean_inc(v_levelMap_4665_);
lean_inc(v_nameMap_4664_);
lean_inc(v_stream_4663_);
lean_dec(v_snd_4658_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4684_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v___x_4673_ = lean_box(0);
v___x_4674_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4666_, v_a_4420_, v_fst_4659_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 3, v___x_4674_);
v___x_4676_ = v___x_4671_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_stream_4663_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_nameMap_4664_);
lean_ctor_set(v_reuseFailAlloc_4683_, 2, v_levelMap_4665_);
lean_ctor_set(v_reuseFailAlloc_4683_, 3, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4683_, 4, v_recursorRuleMap_4667_);
lean_ctor_set(v_reuseFailAlloc_4683_, 5, v_constMap_4668_);
lean_ctor_set(v_reuseFailAlloc_4683_, 6, v_constOrder_4669_);
v___x_4676_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4678_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 1, v___x_4676_);
lean_ctor_set(v___x_4661_, 0, v___x_4673_);
v___x_4678_ = v___x_4661_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4673_);
lean_ctor_set(v_reuseFailAlloc_4682_, 1, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4680_; 
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4678_);
v___x_4680_ = v___x_4656_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec(v_a_4420_);
v_a_4687_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4653_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4653_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4695_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4695_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprLam(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4728_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4698_ = v___x_4695_;
v_isShared_4699_ = v_isSharedCheck_4728_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4695_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4728_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_snd_4700_; lean_object* v_fst_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4727_; 
v_snd_4700_ = lean_ctor_get(v_a_4696_, 1);
v_fst_4701_ = lean_ctor_get(v_a_4696_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_a_4696_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4703_ = v_a_4696_;
v_isShared_4704_ = v_isSharedCheck_4727_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_snd_4700_);
lean_inc(v_fst_4701_);
lean_dec(v_a_4696_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4727_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v_stream_4705_; lean_object* v_nameMap_4706_; lean_object* v_levelMap_4707_; lean_object* v_exprMap_4708_; lean_object* v_recursorRuleMap_4709_; lean_object* v_constMap_4710_; lean_object* v_constOrder_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4726_; 
v_stream_4705_ = lean_ctor_get(v_snd_4700_, 0);
v_nameMap_4706_ = lean_ctor_get(v_snd_4700_, 1);
v_levelMap_4707_ = lean_ctor_get(v_snd_4700_, 2);
v_exprMap_4708_ = lean_ctor_get(v_snd_4700_, 3);
v_recursorRuleMap_4709_ = lean_ctor_get(v_snd_4700_, 4);
v_constMap_4710_ = lean_ctor_get(v_snd_4700_, 5);
v_constOrder_4711_ = lean_ctor_get(v_snd_4700_, 6);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_snd_4700_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4713_ = v_snd_4700_;
v_isShared_4714_ = v_isSharedCheck_4726_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_constOrder_4711_);
lean_inc(v_constMap_4710_);
lean_inc(v_recursorRuleMap_4709_);
lean_inc(v_exprMap_4708_);
lean_inc(v_levelMap_4707_);
lean_inc(v_nameMap_4706_);
lean_inc(v_stream_4705_);
lean_dec(v_snd_4700_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4726_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4715_ = lean_box(0);
v___x_4716_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4708_, v_a_4420_, v_fst_4701_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 3, v___x_4716_);
v___x_4718_ = v___x_4713_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_stream_4705_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_nameMap_4706_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_levelMap_4707_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_recursorRuleMap_4709_);
lean_ctor_set(v_reuseFailAlloc_4725_, 5, v_constMap_4710_);
lean_ctor_set(v_reuseFailAlloc_4725_, 6, v_constOrder_4711_);
v___x_4718_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; 
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 1, v___x_4718_);
lean_ctor_set(v___x_4703_, 0, v___x_4715_);
v___x_4720_ = v___x_4703_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v___x_4718_);
v___x_4720_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4722_; 
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 0, v___x_4720_);
v___x_4722_ = v___x_4698_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4720_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec(v_a_4420_);
v_a_4729_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4695_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4695_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4737_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4737_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprApp(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4770_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4770_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4770_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v_snd_4742_; lean_object* v_fst_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4769_; 
v_snd_4742_ = lean_ctor_get(v_a_4738_, 1);
v_fst_4743_ = lean_ctor_get(v_a_4738_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_a_4738_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4745_ = v_a_4738_;
v_isShared_4746_ = v_isSharedCheck_4769_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_snd_4742_);
lean_inc(v_fst_4743_);
lean_dec(v_a_4738_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4769_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_stream_4747_; lean_object* v_nameMap_4748_; lean_object* v_levelMap_4749_; lean_object* v_exprMap_4750_; lean_object* v_recursorRuleMap_4751_; lean_object* v_constMap_4752_; lean_object* v_constOrder_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4768_; 
v_stream_4747_ = lean_ctor_get(v_snd_4742_, 0);
v_nameMap_4748_ = lean_ctor_get(v_snd_4742_, 1);
v_levelMap_4749_ = lean_ctor_get(v_snd_4742_, 2);
v_exprMap_4750_ = lean_ctor_get(v_snd_4742_, 3);
v_recursorRuleMap_4751_ = lean_ctor_get(v_snd_4742_, 4);
v_constMap_4752_ = lean_ctor_get(v_snd_4742_, 5);
v_constOrder_4753_ = lean_ctor_get(v_snd_4742_, 6);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_snd_4742_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4755_ = v_snd_4742_;
v_isShared_4756_ = v_isSharedCheck_4768_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_constOrder_4753_);
lean_inc(v_constMap_4752_);
lean_inc(v_recursorRuleMap_4751_);
lean_inc(v_exprMap_4750_);
lean_inc(v_levelMap_4749_);
lean_inc(v_nameMap_4748_);
lean_inc(v_stream_4747_);
lean_dec(v_snd_4742_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4768_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4757_ = lean_box(0);
v___x_4758_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4750_, v_a_4420_, v_fst_4743_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 3, v___x_4758_);
v___x_4760_ = v___x_4755_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_stream_4747_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_nameMap_4748_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_levelMap_4749_);
lean_ctor_set(v_reuseFailAlloc_4767_, 3, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4767_, 4, v_recursorRuleMap_4751_);
lean_ctor_set(v_reuseFailAlloc_4767_, 5, v_constMap_4752_);
lean_ctor_set(v_reuseFailAlloc_4767_, 6, v_constOrder_4753_);
v___x_4760_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 1, v___x_4760_);
lean_ctor_set(v___x_4745_, 0, v___x_4757_);
v___x_4762_ = v___x_4745_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4757_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4764_; 
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v___x_4762_);
v___x_4764_ = v___x_4740_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec(v_a_4420_);
v_a_4771_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4737_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4737_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4779_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4779_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprConst(v_snd_4419_, v_a_4348_);
lean_dec(v_snd_4419_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4812_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4812_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4812_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v_snd_4784_; lean_object* v_fst_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4811_; 
v_snd_4784_ = lean_ctor_get(v_a_4780_, 1);
v_fst_4785_ = lean_ctor_get(v_a_4780_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v_a_4780_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4787_ = v_a_4780_;
v_isShared_4788_ = v_isSharedCheck_4811_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_snd_4784_);
lean_inc(v_fst_4785_);
lean_dec(v_a_4780_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4811_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_stream_4789_; lean_object* v_nameMap_4790_; lean_object* v_levelMap_4791_; lean_object* v_exprMap_4792_; lean_object* v_recursorRuleMap_4793_; lean_object* v_constMap_4794_; lean_object* v_constOrder_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4810_; 
v_stream_4789_ = lean_ctor_get(v_snd_4784_, 0);
v_nameMap_4790_ = lean_ctor_get(v_snd_4784_, 1);
v_levelMap_4791_ = lean_ctor_get(v_snd_4784_, 2);
v_exprMap_4792_ = lean_ctor_get(v_snd_4784_, 3);
v_recursorRuleMap_4793_ = lean_ctor_get(v_snd_4784_, 4);
v_constMap_4794_ = lean_ctor_get(v_snd_4784_, 5);
v_constOrder_4795_ = lean_ctor_get(v_snd_4784_, 6);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_snd_4784_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4797_ = v_snd_4784_;
v_isShared_4798_ = v_isSharedCheck_4810_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_constOrder_4795_);
lean_inc(v_constMap_4794_);
lean_inc(v_recursorRuleMap_4793_);
lean_inc(v_exprMap_4792_);
lean_inc(v_levelMap_4791_);
lean_inc(v_nameMap_4790_);
lean_inc(v_stream_4789_);
lean_dec(v_snd_4784_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4810_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
v___x_4799_ = lean_box(0);
v___x_4800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4792_, v_a_4420_, v_fst_4785_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 3, v___x_4800_);
v___x_4802_ = v___x_4797_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_stream_4789_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_nameMap_4790_);
lean_ctor_set(v_reuseFailAlloc_4809_, 2, v_levelMap_4791_);
lean_ctor_set(v_reuseFailAlloc_4809_, 3, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4809_, 4, v_recursorRuleMap_4793_);
lean_ctor_set(v_reuseFailAlloc_4809_, 5, v_constMap_4794_);
lean_ctor_set(v_reuseFailAlloc_4809_, 6, v_constOrder_4795_);
v___x_4802_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 1, v___x_4802_);
lean_ctor_set(v___x_4787_, 0, v___x_4799_);
v___x_4804_ = v___x_4787_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4806_; 
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4804_);
v___x_4806_ = v___x_4782_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec(v_a_4420_);
v_a_4813_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4779_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4779_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4821_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4821_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprSort(v_snd_4419_, v_a_4348_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4854_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4824_ = v___x_4821_;
v_isShared_4825_ = v_isSharedCheck_4854_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4821_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4854_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v_snd_4826_; lean_object* v_fst_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4853_; 
v_snd_4826_ = lean_ctor_get(v_a_4822_, 1);
v_fst_4827_ = lean_ctor_get(v_a_4822_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_a_4822_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4829_ = v_a_4822_;
v_isShared_4830_ = v_isSharedCheck_4853_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_snd_4826_);
lean_inc(v_fst_4827_);
lean_dec(v_a_4822_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4853_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v_stream_4831_; lean_object* v_nameMap_4832_; lean_object* v_levelMap_4833_; lean_object* v_exprMap_4834_; lean_object* v_recursorRuleMap_4835_; lean_object* v_constMap_4836_; lean_object* v_constOrder_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4852_; 
v_stream_4831_ = lean_ctor_get(v_snd_4826_, 0);
v_nameMap_4832_ = lean_ctor_get(v_snd_4826_, 1);
v_levelMap_4833_ = lean_ctor_get(v_snd_4826_, 2);
v_exprMap_4834_ = lean_ctor_get(v_snd_4826_, 3);
v_recursorRuleMap_4835_ = lean_ctor_get(v_snd_4826_, 4);
v_constMap_4836_ = lean_ctor_get(v_snd_4826_, 5);
v_constOrder_4837_ = lean_ctor_get(v_snd_4826_, 6);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_snd_4826_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4839_ = v_snd_4826_;
v_isShared_4840_ = v_isSharedCheck_4852_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_constOrder_4837_);
lean_inc(v_constMap_4836_);
lean_inc(v_recursorRuleMap_4835_);
lean_inc(v_exprMap_4834_);
lean_inc(v_levelMap_4833_);
lean_inc(v_nameMap_4832_);
lean_inc(v_stream_4831_);
lean_dec(v_snd_4826_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4852_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4841_ = lean_box(0);
v___x_4842_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4834_, v_a_4420_, v_fst_4827_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 3, v___x_4842_);
v___x_4844_ = v___x_4839_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_stream_4831_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_nameMap_4832_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_levelMap_4833_);
lean_ctor_set(v_reuseFailAlloc_4851_, 3, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_4851_, 4, v_recursorRuleMap_4835_);
lean_ctor_set(v_reuseFailAlloc_4851_, 5, v_constMap_4836_);
lean_ctor_set(v_reuseFailAlloc_4851_, 6, v_constOrder_4837_);
v___x_4844_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4846_; 
if (v_isShared_4830_ == 0)
{
lean_ctor_set(v___x_4829_, 1, v___x_4844_);
lean_ctor_set(v___x_4829_, 0, v___x_4841_);
v___x_4846_ = v___x_4829_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4841_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
lean_object* v___x_4848_; 
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v___x_4846_);
v___x_4848_ = v___x_4824_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec(v_a_4420_);
v_a_4855_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4821_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4821_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4418_);
if (lean_obj_tag(v_tail_4417_) == 0)
{
lean_object* v___x_4863_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4863_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseExprBVar(v_snd_4419_, v_a_4348_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4896_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4866_ = v___x_4863_;
v_isShared_4867_ = v_isSharedCheck_4896_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4863_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4896_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v_snd_4868_; lean_object* v_fst_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4895_; 
v_snd_4868_ = lean_ctor_get(v_a_4864_, 1);
v_fst_4869_ = lean_ctor_get(v_a_4864_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_a_4864_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4871_ = v_a_4864_;
v_isShared_4872_ = v_isSharedCheck_4895_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_snd_4868_);
lean_inc(v_fst_4869_);
lean_dec(v_a_4864_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4895_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v_stream_4873_; lean_object* v_nameMap_4874_; lean_object* v_levelMap_4875_; lean_object* v_exprMap_4876_; lean_object* v_recursorRuleMap_4877_; lean_object* v_constMap_4878_; lean_object* v_constOrder_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4894_; 
v_stream_4873_ = lean_ctor_get(v_snd_4868_, 0);
v_nameMap_4874_ = lean_ctor_get(v_snd_4868_, 1);
v_levelMap_4875_ = lean_ctor_get(v_snd_4868_, 2);
v_exprMap_4876_ = lean_ctor_get(v_snd_4868_, 3);
v_recursorRuleMap_4877_ = lean_ctor_get(v_snd_4868_, 4);
v_constMap_4878_ = lean_ctor_get(v_snd_4868_, 5);
v_constOrder_4879_ = lean_ctor_get(v_snd_4868_, 6);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_snd_4868_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4881_ = v_snd_4868_;
v_isShared_4882_ = v_isSharedCheck_4894_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_constOrder_4879_);
lean_inc(v_constMap_4878_);
lean_inc(v_recursorRuleMap_4877_);
lean_inc(v_exprMap_4876_);
lean_inc(v_levelMap_4875_);
lean_inc(v_nameMap_4874_);
lean_inc(v_stream_4873_);
lean_dec(v_snd_4868_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4894_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4883_ = lean_box(0);
v___x_4884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_exprMap_4876_, v_a_4420_, v_fst_4869_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 3, v___x_4884_);
v___x_4886_ = v___x_4881_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_stream_4873_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v_nameMap_4874_);
lean_ctor_set(v_reuseFailAlloc_4893_, 2, v_levelMap_4875_);
lean_ctor_set(v_reuseFailAlloc_4893_, 3, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4893_, 4, v_recursorRuleMap_4877_);
lean_ctor_set(v_reuseFailAlloc_4893_, 5, v_constMap_4878_);
lean_ctor_set(v_reuseFailAlloc_4893_, 6, v_constOrder_4879_);
v___x_4886_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
lean_object* v___x_4888_; 
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 1, v___x_4886_);
lean_ctor_set(v___x_4871_, 0, v___x_4883_);
v___x_4888_ = v___x_4871_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4890_; 
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 0, v___x_4888_);
v___x_4890_ = v___x_4866_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec(v_a_4420_);
v_a_4897_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4863_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4863_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
lean_dec(v_snd_4419_);
lean_dec(v_tail_4417_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_mantissa_4410_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_exponent_4411_);
lean_dec(v_mantissa_4410_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 2)
{
lean_object* v_n_4905_; lean_object* v_mantissa_4906_; lean_object* v_exponent_4907_; lean_object* v_natZero_4908_; lean_object* v_intZero_4909_; uint8_t v_isNeg_4910_; 
v_n_4905_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc_ref(v_n_4905_);
lean_dec_ref_known(v_snd_4377_, 1);
v_mantissa_4906_ = lean_ctor_get(v_n_4905_, 0);
lean_inc(v_mantissa_4906_);
v_exponent_4907_ = lean_ctor_get(v_n_4905_, 1);
lean_inc(v_exponent_4907_);
lean_dec_ref(v_n_4905_);
v_natZero_4908_ = lean_unsigned_to_nat(0u);
v_intZero_4909_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_4910_ = lean_int_dec_lt(v_mantissa_4906_, v_intZero_4909_);
if (v_isNeg_4910_ == 0)
{
uint8_t v___x_4911_; 
v___x_4911_ = lean_nat_dec_eq(v_exponent_4907_, v_natZero_4908_);
lean_dec(v_exponent_4907_);
if (v___x_4911_ == 0)
{
lean_dec(v_mantissa_4906_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_4378_) == 1)
{
lean_object* v_head_4912_; lean_object* v_tail_4913_; lean_object* v_fst_4914_; lean_object* v_snd_4915_; lean_object* v_a_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v_head_4912_ = lean_ctor_get(v_tail_4378_, 0);
lean_inc(v_head_4912_);
v_tail_4913_ = lean_ctor_get(v_tail_4378_, 1);
lean_inc(v_tail_4913_);
lean_dec_ref_known(v_tail_4378_, 2);
v_fst_4914_ = lean_ctor_get(v_head_4912_, 0);
lean_inc(v_fst_4914_);
v_snd_4915_ = lean_ctor_get(v_head_4912_, 1);
lean_inc(v_snd_4915_);
lean_dec(v_head_4912_);
v_a_4916_ = lean_nat_abs(v_mantissa_4906_);
lean_dec(v_mantissa_4906_);
v___x_4917_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__20));
v___x_4918_ = lean_string_dec_eq(v_fst_4914_, v___x_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4919_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__21));
v___x_4920_ = lean_string_dec_eq(v_fst_4914_, v___x_4919_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; uint8_t v___x_4922_; 
v___x_4921_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__22));
v___x_4922_ = lean_string_dec_eq(v_fst_4914_, v___x_4921_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__23));
v___x_4924_ = lean_string_dec_eq(v_fst_4914_, v___x_4923_);
lean_dec(v_fst_4914_);
if (v___x_4924_ == 0)
{
lean_dec(v_a_4916_);
lean_dec(v_snd_4915_);
lean_dec(v_tail_4913_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_4913_) == 0)
{
lean_object* v___x_4925_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4925_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelParam(v_snd_4915_, v_a_4348_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4958_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_4958_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4958_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_snd_4930_; lean_object* v_fst_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4957_; 
v_snd_4930_ = lean_ctor_get(v_a_4926_, 1);
v_fst_4931_ = lean_ctor_get(v_a_4926_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v_a_4926_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4933_ = v_a_4926_;
v_isShared_4934_ = v_isSharedCheck_4957_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_snd_4930_);
lean_inc(v_fst_4931_);
lean_dec(v_a_4926_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4957_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v_stream_4935_; lean_object* v_nameMap_4936_; lean_object* v_levelMap_4937_; lean_object* v_exprMap_4938_; lean_object* v_recursorRuleMap_4939_; lean_object* v_constMap_4940_; lean_object* v_constOrder_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4956_; 
v_stream_4935_ = lean_ctor_get(v_snd_4930_, 0);
v_nameMap_4936_ = lean_ctor_get(v_snd_4930_, 1);
v_levelMap_4937_ = lean_ctor_get(v_snd_4930_, 2);
v_exprMap_4938_ = lean_ctor_get(v_snd_4930_, 3);
v_recursorRuleMap_4939_ = lean_ctor_get(v_snd_4930_, 4);
v_constMap_4940_ = lean_ctor_get(v_snd_4930_, 5);
v_constOrder_4941_ = lean_ctor_get(v_snd_4930_, 6);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_snd_4930_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4943_ = v_snd_4930_;
v_isShared_4944_ = v_isSharedCheck_4956_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_constOrder_4941_);
lean_inc(v_constMap_4940_);
lean_inc(v_recursorRuleMap_4939_);
lean_inc(v_exprMap_4938_);
lean_inc(v_levelMap_4937_);
lean_inc(v_nameMap_4936_);
lean_inc(v_stream_4935_);
lean_dec(v_snd_4930_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4956_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4945_ = lean_box(0);
v___x_4946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_4937_, v_a_4916_, v_fst_4931_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 2, v___x_4946_);
v___x_4948_ = v___x_4943_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_stream_4935_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_nameMap_4936_);
lean_ctor_set(v_reuseFailAlloc_4955_, 2, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4955_, 3, v_exprMap_4938_);
lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_recursorRuleMap_4939_);
lean_ctor_set(v_reuseFailAlloc_4955_, 5, v_constMap_4940_);
lean_ctor_set(v_reuseFailAlloc_4955_, 6, v_constOrder_4941_);
v___x_4948_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4950_; 
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 1, v___x_4948_);
lean_ctor_set(v___x_4933_, 0, v___x_4945_);
v___x_4950_ = v___x_4933_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v___x_4948_);
v___x_4950_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
lean_object* v___x_4952_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4950_);
v___x_4952_ = v___x_4928_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4950_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v_a_4916_);
v_a_4959_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4925_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4925_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
else
{
lean_dec(v_a_4916_);
lean_dec(v_snd_4915_);
lean_dec(v_tail_4913_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4914_);
if (lean_obj_tag(v_tail_4913_) == 0)
{
lean_object* v___x_4967_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_4967_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelImax(v_snd_4915_, v_a_4348_);
lean_dec(v_snd_4915_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_5000_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_5000_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_5000_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v_snd_4972_; lean_object* v_fst_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4999_; 
v_snd_4972_ = lean_ctor_get(v_a_4968_, 1);
v_fst_4973_ = lean_ctor_get(v_a_4968_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_a_4968_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4975_ = v_a_4968_;
v_isShared_4976_ = v_isSharedCheck_4999_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_snd_4972_);
lean_inc(v_fst_4973_);
lean_dec(v_a_4968_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4999_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v_stream_4977_; lean_object* v_nameMap_4978_; lean_object* v_levelMap_4979_; lean_object* v_exprMap_4980_; lean_object* v_recursorRuleMap_4981_; lean_object* v_constMap_4982_; lean_object* v_constOrder_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4998_; 
v_stream_4977_ = lean_ctor_get(v_snd_4972_, 0);
v_nameMap_4978_ = lean_ctor_get(v_snd_4972_, 1);
v_levelMap_4979_ = lean_ctor_get(v_snd_4972_, 2);
v_exprMap_4980_ = lean_ctor_get(v_snd_4972_, 3);
v_recursorRuleMap_4981_ = lean_ctor_get(v_snd_4972_, 4);
v_constMap_4982_ = lean_ctor_get(v_snd_4972_, 5);
v_constOrder_4983_ = lean_ctor_get(v_snd_4972_, 6);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_snd_4972_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4985_ = v_snd_4972_;
v_isShared_4986_ = v_isSharedCheck_4998_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_constOrder_4983_);
lean_inc(v_constMap_4982_);
lean_inc(v_recursorRuleMap_4981_);
lean_inc(v_exprMap_4980_);
lean_inc(v_levelMap_4979_);
lean_inc(v_nameMap_4978_);
lean_inc(v_stream_4977_);
lean_dec(v_snd_4972_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4998_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; 
v___x_4987_ = lean_box(0);
v___x_4988_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_4979_, v_a_4916_, v_fst_4973_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 2, v___x_4988_);
v___x_4990_ = v___x_4985_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_stream_4977_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_nameMap_4978_);
lean_ctor_set(v_reuseFailAlloc_4997_, 2, v___x_4988_);
lean_ctor_set(v_reuseFailAlloc_4997_, 3, v_exprMap_4980_);
lean_ctor_set(v_reuseFailAlloc_4997_, 4, v_recursorRuleMap_4981_);
lean_ctor_set(v_reuseFailAlloc_4997_, 5, v_constMap_4982_);
lean_ctor_set(v_reuseFailAlloc_4997_, 6, v_constOrder_4983_);
v___x_4990_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
lean_object* v___x_4992_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_4990_);
lean_ctor_set(v___x_4975_, 0, v___x_4987_);
v___x_4992_ = v___x_4975_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4990_);
v___x_4992_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4994_; 
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 0, v___x_4992_);
v___x_4994_ = v___x_4970_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_dec(v_a_4916_);
v_a_5001_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_4967_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4967_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
else
{
lean_dec(v_a_4916_);
lean_dec(v_snd_4915_);
lean_dec(v_tail_4913_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4914_);
if (lean_obj_tag(v_tail_4913_) == 0)
{
lean_object* v___x_5009_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_5009_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelMax(v_snd_4915_, v_a_4348_);
lean_dec(v_snd_4915_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5042_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5012_ = v___x_5009_;
v_isShared_5013_ = v_isSharedCheck_5042_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5009_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5042_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v_snd_5014_; lean_object* v_fst_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5041_; 
v_snd_5014_ = lean_ctor_get(v_a_5010_, 1);
v_fst_5015_ = lean_ctor_get(v_a_5010_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v_a_5010_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5017_ = v_a_5010_;
v_isShared_5018_ = v_isSharedCheck_5041_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_snd_5014_);
lean_inc(v_fst_5015_);
lean_dec(v_a_5010_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5041_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v_stream_5019_; lean_object* v_nameMap_5020_; lean_object* v_levelMap_5021_; lean_object* v_exprMap_5022_; lean_object* v_recursorRuleMap_5023_; lean_object* v_constMap_5024_; lean_object* v_constOrder_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5040_; 
v_stream_5019_ = lean_ctor_get(v_snd_5014_, 0);
v_nameMap_5020_ = lean_ctor_get(v_snd_5014_, 1);
v_levelMap_5021_ = lean_ctor_get(v_snd_5014_, 2);
v_exprMap_5022_ = lean_ctor_get(v_snd_5014_, 3);
v_recursorRuleMap_5023_ = lean_ctor_get(v_snd_5014_, 4);
v_constMap_5024_ = lean_ctor_get(v_snd_5014_, 5);
v_constOrder_5025_ = lean_ctor_get(v_snd_5014_, 6);
v_isSharedCheck_5040_ = !lean_is_exclusive(v_snd_5014_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5027_ = v_snd_5014_;
v_isShared_5028_ = v_isSharedCheck_5040_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_constOrder_5025_);
lean_inc(v_constMap_5024_);
lean_inc(v_recursorRuleMap_5023_);
lean_inc(v_exprMap_5022_);
lean_inc(v_levelMap_5021_);
lean_inc(v_nameMap_5020_);
lean_inc(v_stream_5019_);
lean_dec(v_snd_5014_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5040_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5029_ = lean_box(0);
v___x_5030_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5021_, v_a_4916_, v_fst_5015_);
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 2, v___x_5030_);
v___x_5032_ = v___x_5027_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_stream_5019_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v_nameMap_5020_);
lean_ctor_set(v_reuseFailAlloc_5039_, 2, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5039_, 3, v_exprMap_5022_);
lean_ctor_set(v_reuseFailAlloc_5039_, 4, v_recursorRuleMap_5023_);
lean_ctor_set(v_reuseFailAlloc_5039_, 5, v_constMap_5024_);
lean_ctor_set(v_reuseFailAlloc_5039_, 6, v_constOrder_5025_);
v___x_5032_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5034_; 
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 1, v___x_5032_);
lean_ctor_set(v___x_5017_, 0, v___x_5029_);
v___x_5034_ = v___x_5017_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5029_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5036_; 
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 0, v___x_5034_);
v___x_5036_ = v___x_5012_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
lean_dec(v_a_4916_);
v_a_5043_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v___x_5009_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5009_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
else
{
lean_dec(v_a_4916_);
lean_dec(v_snd_4915_);
lean_dec(v_tail_4913_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_4914_);
if (lean_obj_tag(v_tail_4913_) == 0)
{
lean_object* v___x_5051_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_5051_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseLevelSucc(v_snd_4915_, v_a_4348_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5084_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5054_ = v___x_5051_;
v_isShared_5055_ = v_isSharedCheck_5084_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5051_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5084_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v_snd_5056_; lean_object* v_fst_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5083_; 
v_snd_5056_ = lean_ctor_get(v_a_5052_, 1);
v_fst_5057_ = lean_ctor_get(v_a_5052_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v_a_5052_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5059_ = v_a_5052_;
v_isShared_5060_ = v_isSharedCheck_5083_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_snd_5056_);
lean_inc(v_fst_5057_);
lean_dec(v_a_5052_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5083_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v_stream_5061_; lean_object* v_nameMap_5062_; lean_object* v_levelMap_5063_; lean_object* v_exprMap_5064_; lean_object* v_recursorRuleMap_5065_; lean_object* v_constMap_5066_; lean_object* v_constOrder_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5082_; 
v_stream_5061_ = lean_ctor_get(v_snd_5056_, 0);
v_nameMap_5062_ = lean_ctor_get(v_snd_5056_, 1);
v_levelMap_5063_ = lean_ctor_get(v_snd_5056_, 2);
v_exprMap_5064_ = lean_ctor_get(v_snd_5056_, 3);
v_recursorRuleMap_5065_ = lean_ctor_get(v_snd_5056_, 4);
v_constMap_5066_ = lean_ctor_get(v_snd_5056_, 5);
v_constOrder_5067_ = lean_ctor_get(v_snd_5056_, 6);
v_isSharedCheck_5082_ = !lean_is_exclusive(v_snd_5056_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5069_ = v_snd_5056_;
v_isShared_5070_ = v_isSharedCheck_5082_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_constOrder_5067_);
lean_inc(v_constMap_5066_);
lean_inc(v_recursorRuleMap_5065_);
lean_inc(v_exprMap_5064_);
lean_inc(v_levelMap_5063_);
lean_inc(v_nameMap_5062_);
lean_inc(v_stream_5061_);
lean_dec(v_snd_5056_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5082_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5071_ = lean_box(0);
v___x_5072_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_levelMap_5063_, v_a_4916_, v_fst_5057_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 2, v___x_5072_);
v___x_5074_ = v___x_5069_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_stream_5061_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v_nameMap_5062_);
lean_ctor_set(v_reuseFailAlloc_5081_, 2, v___x_5072_);
lean_ctor_set(v_reuseFailAlloc_5081_, 3, v_exprMap_5064_);
lean_ctor_set(v_reuseFailAlloc_5081_, 4, v_recursorRuleMap_5065_);
lean_ctor_set(v_reuseFailAlloc_5081_, 5, v_constMap_5066_);
lean_ctor_set(v_reuseFailAlloc_5081_, 6, v_constOrder_5067_);
v___x_5074_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5076_; 
if (v_isShared_5060_ == 0)
{
lean_ctor_set(v___x_5059_, 1, v___x_5074_);
lean_ctor_set(v___x_5059_, 0, v___x_5071_);
v___x_5076_ = v___x_5059_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5078_; 
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5076_);
v___x_5078_ = v___x_5054_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_a_4916_);
v_a_5085_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5051_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5051_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_dec(v_a_4916_);
lean_dec(v_snd_4915_);
lean_dec(v_tail_4913_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_mantissa_4906_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_exponent_4907_);
lean_dec(v_mantissa_4906_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec_ref(v_fst_4376_);
if (lean_obj_tag(v_snd_4377_) == 2)
{
lean_object* v_n_5093_; lean_object* v_mantissa_5094_; lean_object* v_exponent_5095_; lean_object* v_natZero_5096_; lean_object* v_intZero_5097_; uint8_t v_isNeg_5098_; 
v_n_5093_ = lean_ctor_get(v_snd_4377_, 0);
lean_inc_ref(v_n_5093_);
lean_dec_ref_known(v_snd_4377_, 1);
v_mantissa_5094_ = lean_ctor_get(v_n_5093_, 0);
lean_inc(v_mantissa_5094_);
v_exponent_5095_ = lean_ctor_get(v_n_5093_, 1);
lean_inc(v_exponent_5095_);
lean_dec_ref(v_n_5093_);
v_natZero_5096_ = lean_unsigned_to_nat(0u);
v_intZero_5097_ = lean_obj_once(&l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3, &l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3_once, _init_l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__3);
v_isNeg_5098_ = lean_int_dec_lt(v_mantissa_5094_, v_intZero_5097_);
if (v_isNeg_5098_ == 0)
{
uint8_t v___x_5099_; 
v___x_5099_ = lean_nat_dec_eq(v_exponent_5095_, v_natZero_5096_);
lean_dec(v_exponent_5095_);
if (v___x_5099_ == 0)
{
lean_dec(v_mantissa_5094_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_4378_) == 1)
{
lean_object* v_head_5100_; lean_object* v_tail_5101_; lean_object* v_fst_5102_; lean_object* v_snd_5103_; lean_object* v_a_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
v_head_5100_ = lean_ctor_get(v_tail_4378_, 0);
lean_inc(v_head_5100_);
v_tail_5101_ = lean_ctor_get(v_tail_4378_, 1);
lean_inc(v_tail_5101_);
lean_dec_ref_known(v_tail_4378_, 2);
v_fst_5102_ = lean_ctor_get(v_head_5100_, 0);
lean_inc(v_fst_5102_);
v_snd_5103_ = lean_ctor_get(v_head_5100_, 1);
lean_inc(v_snd_5103_);
lean_dec(v_head_5100_);
v_a_5104_ = lean_nat_abs(v_mantissa_5094_);
lean_dec(v_mantissa_5094_);
v___x_5105_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr___closed__4));
v___x_5106_ = lean_string_dec_eq(v_fst_5102_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; uint8_t v___x_5108_; 
v___x_5107_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___closed__24));
v___x_5108_ = lean_string_dec_eq(v_fst_5102_, v___x_5107_);
lean_dec(v_fst_5102_);
if (v___x_5108_ == 0)
{
lean_dec(v_a_5104_);
lean_dec(v_snd_5103_);
lean_dec(v_tail_5101_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
else
{
if (lean_obj_tag(v_tail_5101_) == 0)
{
lean_object* v___x_5109_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_5109_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameNum(v_snd_5103_, v_a_4348_);
lean_dec(v_snd_5103_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5142_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5112_ = v___x_5109_;
v_isShared_5113_ = v_isSharedCheck_5142_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5109_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5142_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_snd_5114_; lean_object* v_fst_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5141_; 
v_snd_5114_ = lean_ctor_get(v_a_5110_, 1);
v_fst_5115_ = lean_ctor_get(v_a_5110_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v_a_5110_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5117_ = v_a_5110_;
v_isShared_5118_ = v_isSharedCheck_5141_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_snd_5114_);
lean_inc(v_fst_5115_);
lean_dec(v_a_5110_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5141_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v_stream_5119_; lean_object* v_nameMap_5120_; lean_object* v_levelMap_5121_; lean_object* v_exprMap_5122_; lean_object* v_recursorRuleMap_5123_; lean_object* v_constMap_5124_; lean_object* v_constOrder_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5140_; 
v_stream_5119_ = lean_ctor_get(v_snd_5114_, 0);
v_nameMap_5120_ = lean_ctor_get(v_snd_5114_, 1);
v_levelMap_5121_ = lean_ctor_get(v_snd_5114_, 2);
v_exprMap_5122_ = lean_ctor_get(v_snd_5114_, 3);
v_recursorRuleMap_5123_ = lean_ctor_get(v_snd_5114_, 4);
v_constMap_5124_ = lean_ctor_get(v_snd_5114_, 5);
v_constOrder_5125_ = lean_ctor_get(v_snd_5114_, 6);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_snd_5114_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5127_ = v_snd_5114_;
v_isShared_5128_ = v_isSharedCheck_5140_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_constOrder_5125_);
lean_inc(v_constMap_5124_);
lean_inc(v_recursorRuleMap_5123_);
lean_inc(v_exprMap_5122_);
lean_inc(v_levelMap_5121_);
lean_inc(v_nameMap_5120_);
lean_inc(v_stream_5119_);
lean_dec(v_snd_5114_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5140_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5129_ = lean_box(0);
v___x_5130_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5120_, v_a_5104_, v_fst_5115_);
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 1, v___x_5130_);
v___x_5132_ = v___x_5127_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_stream_5119_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_levelMap_5121_);
lean_ctor_set(v_reuseFailAlloc_5139_, 3, v_exprMap_5122_);
lean_ctor_set(v_reuseFailAlloc_5139_, 4, v_recursorRuleMap_5123_);
lean_ctor_set(v_reuseFailAlloc_5139_, 5, v_constMap_5124_);
lean_ctor_set(v_reuseFailAlloc_5139_, 6, v_constOrder_5125_);
v___x_5132_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_object* v___x_5134_; 
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 1, v___x_5132_);
lean_ctor_set(v___x_5117_, 0, v___x_5129_);
v___x_5134_ = v___x_5117_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5129_);
lean_ctor_set(v_reuseFailAlloc_5138_, 1, v___x_5132_);
v___x_5134_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
lean_object* v___x_5136_; 
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 0, v___x_5134_);
v___x_5136_ = v___x_5112_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_a_5104_);
v_a_5143_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5109_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5109_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_dec(v_a_5104_);
lean_dec(v_snd_5103_);
lean_dec(v_tail_5101_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_fst_5102_);
if (lean_obj_tag(v_tail_5101_) == 0)
{
lean_object* v___x_5151_; 
lean_del_object(v___x_4361_);
lean_dec(v_kvPairs_4359_);
lean_del_object(v___x_4357_);
v___x_5151_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseNameStr(v_snd_5103_, v_a_4348_);
lean_dec(v_snd_5103_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5184_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5154_ = v___x_5151_;
v_isShared_5155_ = v_isSharedCheck_5184_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5151_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5184_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v_snd_5156_; lean_object* v_fst_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5183_; 
v_snd_5156_ = lean_ctor_get(v_a_5152_, 1);
v_fst_5157_ = lean_ctor_get(v_a_5152_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v_a_5152_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5159_ = v_a_5152_;
v_isShared_5160_ = v_isSharedCheck_5183_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_snd_5156_);
lean_inc(v_fst_5157_);
lean_dec(v_a_5152_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5183_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v_stream_5161_; lean_object* v_nameMap_5162_; lean_object* v_levelMap_5163_; lean_object* v_exprMap_5164_; lean_object* v_recursorRuleMap_5165_; lean_object* v_constMap_5166_; lean_object* v_constOrder_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5182_; 
v_stream_5161_ = lean_ctor_get(v_snd_5156_, 0);
v_nameMap_5162_ = lean_ctor_get(v_snd_5156_, 1);
v_levelMap_5163_ = lean_ctor_get(v_snd_5156_, 2);
v_exprMap_5164_ = lean_ctor_get(v_snd_5156_, 3);
v_recursorRuleMap_5165_ = lean_ctor_get(v_snd_5156_, 4);
v_constMap_5166_ = lean_ctor_get(v_snd_5156_, 5);
v_constOrder_5167_ = lean_ctor_get(v_snd_5156_, 6);
v_isSharedCheck_5182_ = !lean_is_exclusive(v_snd_5156_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5169_ = v_snd_5156_;
v_isShared_5170_ = v_isSharedCheck_5182_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_constOrder_5167_);
lean_inc(v_constMap_5166_);
lean_inc(v_recursorRuleMap_5165_);
lean_inc(v_exprMap_5164_);
lean_inc(v_levelMap_5163_);
lean_inc(v_nameMap_5162_);
lean_inc(v_stream_5161_);
lean_dec(v_snd_5156_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5182_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5174_; 
v___x_5171_ = lean_box(0);
v___x_5172_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Parse_0__LeanExport_Parse_M_run_spec__0___redArg(v_nameMap_5162_, v_a_5104_, v_fst_5157_);
if (v_isShared_5170_ == 0)
{
lean_ctor_set(v___x_5169_, 1, v___x_5172_);
v___x_5174_ = v___x_5169_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_stream_5161_);
lean_ctor_set(v_reuseFailAlloc_5181_, 1, v___x_5172_);
lean_ctor_set(v_reuseFailAlloc_5181_, 2, v_levelMap_5163_);
lean_ctor_set(v_reuseFailAlloc_5181_, 3, v_exprMap_5164_);
lean_ctor_set(v_reuseFailAlloc_5181_, 4, v_recursorRuleMap_5165_);
lean_ctor_set(v_reuseFailAlloc_5181_, 5, v_constMap_5166_);
lean_ctor_set(v_reuseFailAlloc_5181_, 6, v_constOrder_5167_);
v___x_5174_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5176_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 1, v___x_5174_);
lean_ctor_set(v___x_5159_, 0, v___x_5171_);
v___x_5176_ = v___x_5159_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v___x_5174_);
v___x_5176_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
lean_object* v___x_5178_; 
if (v_isShared_5155_ == 0)
{
lean_ctor_set(v___x_5154_, 0, v___x_5176_);
v___x_5178_ = v___x_5154_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
lean_dec(v_a_5104_);
v_a_5185_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5151_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5151_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
else
{
lean_dec(v_a_5104_);
lean_dec(v_snd_5103_);
lean_dec(v_tail_5101_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_mantissa_5094_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
else
{
lean_dec(v_exponent_5095_);
lean_dec(v_mantissa_5094_);
lean_dec(v_tail_4378_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v_tail_4378_);
lean_dec(v_snd_4377_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
v___jp_5193_:
{
if (lean_obj_tag(v___y_5194_) == 1)
{
lean_object* v_head_5195_; lean_object* v_tail_5196_; lean_object* v_fst_5197_; lean_object* v_snd_5198_; 
v_head_5195_ = lean_ctor_get(v___y_5194_, 0);
lean_inc(v_head_5195_);
v_tail_5196_ = lean_ctor_get(v___y_5194_, 1);
lean_inc(v_tail_5196_);
lean_dec_ref_known(v___y_5194_, 2);
v_fst_5197_ = lean_ctor_get(v_head_5195_, 0);
lean_inc(v_fst_5197_);
v_snd_5198_ = lean_ctor_get(v_head_5195_, 1);
lean_inc(v_snd_5198_);
lean_dec(v_head_5195_);
v_fst_4376_ = v_fst_5197_;
v_snd_4377_ = v_snd_5198_;
v_tail_4378_ = v_tail_5196_;
goto v___jp_4375_;
}
else
{
lean_dec(v___y_5194_);
lean_dec_ref(v_a_4348_);
goto v___jp_4363_;
}
}
}
}
else
{
lean_del_object(v___x_4357_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4348_);
goto v___jp_4350_;
}
}
}
else
{
lean_dec_ref(v___x_4354_);
lean_dec_ref(v_a_4348_);
goto v___jp_4350_;
}
v___jp_4350_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = ((lean_object*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseJsonObj___closed__1));
v___x_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem___boxed(lean_object* v_line_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v_res_5232_; 
v_res_5232_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_line_5229_, v_a_5230_);
return v_res_5232_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(lean_object* v_a_5233_){
_start:
{
lean_object* v_stream_5235_; lean_object* v_getLine_5236_; lean_object* v___x_5237_; 
v_stream_5235_ = lean_ctor_get(v_a_5233_, 0);
v_getLine_5236_ = lean_ctor_get(v_stream_5235_, 3);
lean_inc_ref(v_getLine_5236_);
v___x_5237_ = lean_apply_1(v_getLine_5236_, lean_box(0));
if (lean_obj_tag(v___x_5237_) == 0)
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5254_; 
v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5254_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5254_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; uint8_t v___x_5244_; 
v___x_5242_ = lean_string_utf8_byte_size(v_a_5238_);
v___x_5243_ = lean_unsigned_to_nat(0u);
v___x_5244_ = lean_nat_dec_eq(v___x_5242_, v___x_5243_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; 
lean_del_object(v___x_5240_);
v___x_5245_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItem(v_a_5238_, v_a_5233_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v_snd_5247_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_a_5246_);
lean_dec_ref_known(v___x_5245_, 1);
v_snd_5247_ = lean_ctor_get(v_a_5246_, 1);
lean_inc(v_snd_5247_);
lean_dec(v_a_5246_);
v_a_5233_ = v_snd_5247_;
goto _start;
}
else
{
return v___x_5245_;
}
}
else
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5252_; 
lean_dec(v_a_5238_);
v___x_5249_ = lean_box(0);
v___x_5250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5249_);
lean_ctor_set(v___x_5250_, 1, v_a_5233_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v___x_5250_);
v___x_5252_ = v___x_5240_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5250_);
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
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
lean_dec_ref(v_a_5233_);
v_a_5255_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5237_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5237_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go___boxed(lean_object* v_a_5263_, lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5263_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_a_5266_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems___boxed(lean_object* v_a_5269_, lean_object* v_a_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems(v_a_5269_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(lean_object* v_a_5272_){
_start:
{
lean_object* v_stream_5274_; lean_object* v_getLine_5275_; lean_object* v___x_5276_; 
v_stream_5274_ = lean_ctor_get(v_a_5272_, 0);
v_getLine_5275_ = lean_ctor_get(v_stream_5274_, 3);
lean_inc_ref(v_getLine_5275_);
v___x_5276_ = lean_apply_1(v_getLine_5275_, lean_box(0));
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5285_; 
v_isSharedCheck_5285_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; 
v_unused_5286_ = lean_ctor_get(v___x_5276_, 0);
lean_dec(v_unused_5286_);
v___x_5278_ = v___x_5276_;
v_isShared_5279_ = v_isSharedCheck_5285_;
goto v_resetjp_5277_;
}
else
{
lean_dec(v___x_5276_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5285_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5280_ = lean_box(0);
v___x_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
lean_ctor_set(v___x_5281_, 1, v_a_5272_);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 0, v___x_5281_);
v___x_5283_ = v___x_5278_;
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
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_dec_ref(v_a_5272_);
v_a_5287_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5276_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5276_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata___boxed(lean_object* v_a_5295_, lean_object* v_a_5296_){
_start:
{
lean_object* v_res_5297_; 
v_res_5297_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5295_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(lean_object* v_a_5298_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseMdata(v_a_5298_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; lean_object* v_snd_5302_; lean_object* v___x_5303_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref_known(v___x_5300_, 1);
v_snd_5302_ = lean_ctor_get(v_a_5301_, 1);
lean_inc(v_snd_5302_);
lean_dec(v_a_5301_);
v___x_5303_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseItems_go(v_snd_5302_);
return v___x_5303_;
}
else
{
return v___x_5300_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed(lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile(v_a_5304_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream(lean_object* v_stream_5307_){
_start:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5309_ = lean_alloc_closure((void*)(l___private_LeanExport_Parse_0__LeanExport_Parse_parseFile___boxed), 2, 0);
v___x_5310_ = l___private_LeanExport_Parse_0__LeanExport_Parse_M_run___redArg(v___x_5309_, v_stream_5307_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5329_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5329_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5329_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v_snd_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5327_; 
v_snd_5315_ = lean_ctor_get(v_a_5311_, 1);
v_isSharedCheck_5327_ = !lean_is_exclusive(v_a_5311_);
if (v_isSharedCheck_5327_ == 0)
{
lean_object* v_unused_5328_; 
v_unused_5328_ = lean_ctor_get(v_a_5311_, 0);
lean_dec(v_unused_5328_);
v___x_5317_ = v_a_5311_;
v_isShared_5318_ = v_isSharedCheck_5327_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_snd_5315_);
lean_dec(v_a_5311_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5327_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v_constMap_5319_; lean_object* v_constOrder_5320_; lean_object* v___x_5322_; 
v_constMap_5319_ = lean_ctor_get(v_snd_5315_, 5);
lean_inc_ref(v_constMap_5319_);
v_constOrder_5320_ = lean_ctor_get(v_snd_5315_, 6);
lean_inc_ref(v_constOrder_5320_);
lean_dec(v_snd_5315_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 1, v_constOrder_5320_);
lean_ctor_set(v___x_5317_, 0, v_constMap_5319_);
v___x_5322_ = v___x_5317_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_constMap_5319_);
lean_ctor_set(v_reuseFailAlloc_5326_, 1, v_constOrder_5320_);
v___x_5322_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
lean_object* v___x_5324_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5322_);
v___x_5324_ = v___x_5313_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v_a_5330_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5310_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5310_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_parseStream___boxed(lean_object* v_stream_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_LeanExport_parseStream(v_stream_5338_);
return v_res_5340_;
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

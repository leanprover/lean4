// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpCongrTheorems
// Imports: public import Lean.Util.Recognizers public import Lean.Util.CollectMVars public import Lean.Meta.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorem_default = (const lean_object*)&l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorem = (const lean_object*)&l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "theoremName"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "funName"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "hypothesesPos"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprSimpCongrTheorem_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprSimpCongrTheorem = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lemmas"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSMap"};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprSimpCongrTheorems_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprSimpCongrTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprSimpCongrTheorems = (const lean_object*)&l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "congrExtension"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 78, 117, 200, 251, 75, 97, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addSimpCongrTheoremEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrExtension;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Invalid `congr` theorem: Parameter #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = " is not a valid hypothesis because its right-hand side argument is not a local variable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `congr` theorem: Argument #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " of parameter #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " contains unresolved parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = " is not a valid hypothesis because its right-hand side head was already resolved"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = " is not a valid hypothesis because its right-hand side head is not a metavariable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = " is not a valid hypothesis because its left-hand side contains unresolved parameters"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "Invalid `congr` theorem: The left- and right-hand sides of the equality are not applications of the same function"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSimpCongrTheorem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_mkSimpCongrTheorem___closed__0;
static const lean_string_object l_Lean_Meta_mkSimpCongrTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Invalid `congr` theorem: Theorem is not an equality or iff"};
static const lean_object* l_Lean_Meta_mkSimpCongrTheorem___closed__1 = (const lean_object*)&l_Lean_Meta_mkSimpCongrTheorem___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSimpCongrTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpCongrTheorem___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 9, 234, 253, 232, 127, 99, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SimpCongrTheorems"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 0, 78, 233, 190, 98, 122, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(207, 34, 39, 105, 1, 241, 116, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 50, 129, 254, 87, 32, 156, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 161, 62, 70, 239, 62, 165, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 107, 120, 238, 54, 25, 193, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 115, 140, 210, 180, 224, 162, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 171, 49, 237, 123, 49, 5, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 207, 52, 237, 96, 179, 200, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 160, 83, 152, 87, 168, 44, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 34, 37, 107, 117, 78, 54, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 94, 137, 117, 236, 135, 175, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "congruence theorem"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1291, .m_capacity = 1291, .m_length = 1266, .m_data = "Registers `simp` congruence lemmas.\n\nA `simp` congruence lemma should prove the equality of two applications of the same function from\nthe equality of the individual arguments. They are used by `simp` to visit subexpressions of an\napplication where the default congruence algorithm fails. This is particularly important for\nfunctions where some parameters depend on previous parameters.\n\nCongruence lemmas should have an equality for every parameter, possibly bounded by foralls, with\nthe right hand side being an application of a parameter on the right-hand side. When applying\ncongruence theorems, `simp` will first infer parameters from the right-hand side, then try to\nsimplify each left-hand side of the parameter equalities and finally infer the right-hand side\nparameters from the result.\n\nExample:\n```\ndef Option.pbind (o : Option α) (f : (a : α) → o = some a → Option β) : Option β := ...\n\n@[congr]\ntheorem Option.pbind_congr\n    {o o' : Option α} (ho : o = o') -- equality for first parameter\n    {f : (a : α) → o = some a → Option β} {f' : (a : α) → o' = some a → Option β}\n    (hf : ∀ (a : α) (h : _), f a (ho.trans h) = f' a h) : -- equality for second parameter\n    o.pbind f = o'.pbind f' := -- conclusion: equality of the whole application\n  ...\n```\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__1(lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_to_int(v_a_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Nat_reprFast(v___y_11_);
v___x_13_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_dec(v_x_14_);
return v_x_15_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_29_; 
v_head_17_ = lean_ctor_get(v_x_16_, 0);
v_tail_18_ = lean_ctor_get(v_x_16_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_29_ == 0)
{
v___x_20_ = v_x_16_;
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v_x_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
lean_inc(v_x_14_);
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 5);
lean_ctor_set(v___x_20_, 1, v_x_14_);
lean_ctor_set(v___x_20_, 0, v_x_15_);
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_x_15_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_x_14_);
v___x_23_ = v_reuseFailAlloc_28_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = l_Nat_reprFast(v_head_17_);
v___x_25_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v___x_26_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_23_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v_x_15_ = v___x_26_;
v_x_16_ = v_tail_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2(lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_dec(v_x_30_);
return v_x_31_;
}
else
{
lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_45_; 
v_head_33_ = lean_ctor_get(v_x_32_, 0);
v_tail_34_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_45_ == 0)
{
v___x_36_ = v_x_32_;
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_head_33_);
lean_dec(v_x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
lean_inc(v_x_30_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 5);
lean_ctor_set(v___x_36_, 1, v_x_30_);
lean_ctor_set(v___x_36_, 0, v_x_31_);
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_x_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_x_30_);
v___x_39_ = v_reuseFailAlloc_44_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Nat_reprFast(v_head_33_);
v___x_41_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2_spec__3(v_x_30_, v___x_42_, v_tail_34_);
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_48_; 
lean_dec(v_x_47_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v_tail_49_; 
v_tail_49_ = lean_ctor_get(v_x_46_, 1);
if (lean_obj_tag(v_tail_49_) == 0)
{
lean_object* v_head_50_; lean_object* v___x_51_; 
lean_dec(v_x_47_);
v_head_50_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_50_);
lean_dec_ref_known(v_x_46_, 2);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref_known(v_x_46_, 2);
v___x_53_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(v_head_52_);
v___x_54_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2(v_x_47_, v___x_53_, v_tail_49_);
return v___x_54_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0));
v___x_64_ = lean_string_length(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0(lean_object* v_xs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_get_size(v_xs_74_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_78_ = lean_array_to_list(v_xs_74_);
v___x_79_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3));
v___x_80_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0(v___x_78_, v___x_79_);
v___x_81_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6);
v___x_82_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Std_Format_fill(v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec_ref(v_xs_74_);
v___x_88_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10));
return v___x_88_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(15u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(11u);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(17u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(12u);
v___x_118_ = lean_nat_to_int(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0));
v___x_121_ = lean_string_length(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(lean_object* v_x_128_){
_start:
{
lean_object* v_theoremName_129_; lean_object* v_funName_130_; lean_object* v_hypothesesPos_131_; lean_object* v_priority_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_theoremName_129_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_theoremName_129_);
v_funName_130_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_funName_130_);
v_hypothesesPos_131_ = lean_ctor_get(v_x_128_, 2);
lean_inc_ref(v_hypothesesPos_131_);
v_priority_132_ = lean_ctor_get(v_x_128_, 3);
lean_inc(v_priority_132_);
lean_dec_ref(v_x_128_);
v___x_133_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5));
v___x_134_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6));
v___x_135_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Lean_Name_reprPrec(v_theoremName_129_, v___x_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_135_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_134_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2));
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_box(1);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9));
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_133_);
v___x_149_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10);
v___x_150_ = l_Lean_Name_reprPrec(v_funName_130_, v___x_136_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_139_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_148_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_142_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_144_);
v___x_156_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_133_);
v___x_159_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13);
v___x_160_ = l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0(v_hypothesesPos_131_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_139_);
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_158_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_142_);
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_144_);
v___x_166_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15));
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_133_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16);
v___x_170_ = l_Nat_reprFast(v_priority_132_);
v___x_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_169_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_139_);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_168_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19);
v___x_176_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20));
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_174_);
v___x_178_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21));
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_139_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr(lean_object* v_x_182_, lean_object* v_prec_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorem_repr___boxed(lean_object* v_x_185_, lean_object* v_prec_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_instReprSimpCongrTheorem_repr(v_x_185_, v_prec_186_);
lean_dec(v_prec_186_);
return v_res_187_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_unsigned_to_nat(16u);
v___x_192_ = lean_mk_array(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3);
v___x_200_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1);
v___x_201_ = 1;
v___x_202_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_199_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*2, v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpCongrTheorems(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_dec(v_f_205_);
return v_x_206_;
}
else
{
lean_object* v_key_208_; lean_object* v_value_209_; lean_object* v_tail_210_; lean_object* v___x_211_; 
v_key_208_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_key_208_);
v_value_209_ = lean_ctor_get(v_x_207_, 1);
lean_inc(v_value_209_);
v_tail_210_ = lean_ctor_get(v_x_207_, 2);
lean_inc(v_tail_210_);
lean_dec_ref_known(v_x_207_, 3);
lean_inc(v_f_205_);
v___x_211_ = lean_apply_3(v_f_205_, v_x_206_, v_key_208_, v_value_209_);
v_x_206_ = v___x_211_;
v_x_207_ = v_tail_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(lean_object* v_f_213_, lean_object* v_as_214_, size_t v_i_215_, size_t v_stop_216_, lean_object* v_b_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_eq(v_i_215_, v_stop_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; 
v___x_219_ = lean_array_uget_borrowed(v_as_214_, v_i_215_);
lean_inc(v___x_219_);
lean_inc(v_f_213_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(v_f_213_, v_b_217_, v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_215_, v___x_221_);
v_i_215_ = v___x_222_;
v_b_217_ = v___x_220_;
goto _start;
}
else
{
lean_dec(v_f_213_);
return v_b_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_f_224_, lean_object* v_as_225_, lean_object* v_i_226_, lean_object* v_stop_227_, lean_object* v_b_228_){
_start:
{
size_t v_i_boxed_229_; size_t v_stop_boxed_230_; lean_object* v_res_231_; 
v_i_boxed_229_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_stop_boxed_230_ = lean_unbox_usize(v_stop_227_);
lean_dec(v_stop_227_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_224_, v_as_225_, v_i_boxed_229_, v_stop_boxed_230_, v_b_228_);
lean_dec_ref(v_as_225_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_f_232_, lean_object* v_x1_233_, lean_object* v_x2_234_, lean_object* v_x3_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_3(v_f_232_, v_x1_233_, v_x2_234_, v_x3_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object* v_f_237_, lean_object* v_keys_238_, lean_object* v_vals_239_, lean_object* v_i_240_, lean_object* v_acc_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_keys_238_);
v___x_243_ = lean_nat_dec_lt(v_i_240_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_i_240_);
lean_dec(v_f_237_);
return v_acc_241_;
}
else
{
lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_k_244_ = lean_array_fget_borrowed(v_keys_238_, v_i_240_);
v_v_245_ = lean_array_fget_borrowed(v_vals_239_, v_i_240_);
lean_inc(v_f_237_);
lean_inc(v_v_245_);
lean_inc(v_k_244_);
v___x_246_ = lean_apply_3(v_f_237_, v_acc_241_, v_k_244_, v_v_245_);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v_i_240_, v___x_247_);
lean_dec(v_i_240_);
v_i_240_ = v___x_248_;
v_acc_241_ = v___x_246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object* v_f_250_, lean_object* v_keys_251_, lean_object* v_vals_252_, lean_object* v_i_253_, lean_object* v_acc_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_250_, v_keys_251_, v_vals_252_, v_i_253_, v_acc_254_);
lean_dec_ref(v_vals_252_);
lean_dec_ref(v_keys_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object* v_f_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v_es_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_es_259_ = lean_ctor_get(v_x_257_, 0);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_array_get_size(v_es_259_);
v___x_262_ = lean_nat_dec_lt(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_dec(v_f_256_);
return v_x_258_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_le(v___x_261_, v___x_261_);
if (v___x_263_ == 0)
{
if (v___x_262_ == 0)
{
lean_dec(v_f_256_);
return v_x_258_;
}
else
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_261_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_256_, v_es_259_, v___x_264_, v___x_265_, v_x_258_);
return v___x_266_;
}
}
else
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_261_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_256_, v_es_259_, v___x_267_, v___x_268_, v_x_258_);
return v___x_269_;
}
}
}
else
{
lean_object* v_ks_270_; lean_object* v_vs_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_ks_270_ = lean_ctor_get(v_x_257_, 0);
v_vs_271_ = lean_ctor_get(v_x_257_, 1);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_256_, v_ks_270_, v_vs_271_, v___x_272_, v_x_258_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object* v_f_274_, lean_object* v_as_275_, size_t v_i_276_, size_t v_stop_277_, lean_object* v_b_278_){
_start:
{
lean_object* v___y_280_; uint8_t v___x_284_; 
v___x_284_ = lean_usize_dec_eq(v_i_276_, v_stop_277_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_uget_borrowed(v_as_275_, v_i_276_);
switch(lean_obj_tag(v___x_285_))
{
case 0:
{
lean_object* v_key_286_; lean_object* v_val_287_; lean_object* v___x_288_; 
v_key_286_ = lean_ctor_get(v___x_285_, 0);
v_val_287_ = lean_ctor_get(v___x_285_, 1);
lean_inc(v_f_274_);
lean_inc(v_val_287_);
lean_inc(v_key_286_);
v___x_288_ = lean_apply_3(v_f_274_, v_b_278_, v_key_286_, v_val_287_);
v___y_280_ = v___x_288_;
goto v___jp_279_;
}
case 1:
{
lean_object* v_node_289_; lean_object* v___x_290_; 
v_node_289_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_f_274_);
v___x_290_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_274_, v_node_289_, v_b_278_);
v___y_280_ = v___x_290_;
goto v___jp_279_;
}
default: 
{
v___y_280_ = v_b_278_;
goto v___jp_279_;
}
}
}
else
{
lean_dec(v_f_274_);
return v_b_278_;
}
v___jp_279_:
{
size_t v___x_281_; size_t v___x_282_; 
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_add(v_i_276_, v___x_281_);
v_i_276_ = v___x_282_;
v_b_278_ = v___y_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_f_291_, lean_object* v_as_292_, lean_object* v_i_293_, lean_object* v_stop_294_, lean_object* v_b_295_){
_start:
{
size_t v_i_boxed_296_; size_t v_stop_boxed_297_; lean_object* v_res_298_; 
v_i_boxed_296_ = lean_unbox_usize(v_i_293_);
lean_dec(v_i_293_);
v_stop_boxed_297_ = lean_unbox_usize(v_stop_294_);
lean_dec(v_stop_294_);
v_res_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_291_, v_as_292_, v_i_boxed_296_, v_stop_boxed_297_, v_b_295_);
lean_dec_ref(v_as_292_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_299_, v_x_300_, v_x_301_);
lean_dec_ref(v_x_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_303_, lean_object* v_f_304_, lean_object* v_init_305_){
_start:
{
lean_object* v___f_306_; lean_object* v___x_307_; 
v___f_306_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_306_, 0, v_f_304_);
v___x_307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_306_, v_map_303_, v_init_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_308_, lean_object* v_f_309_, lean_object* v_init_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_308_, v_f_309_, v_init_310_);
lean_dec_ref(v_map_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(lean_object* v_f_312_, lean_object* v_init_313_, lean_object* v_m_314_){
_start:
{
lean_object* v_map_u2081_315_; lean_object* v_map_u2082_316_; lean_object* v_buckets_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_map_u2081_315_ = lean_ctor_get(v_m_314_, 0);
v_map_u2082_316_ = lean_ctor_get(v_m_314_, 1);
v_buckets_317_ = lean_ctor_get(v_map_u2081_315_, 1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_buckets_317_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_316_, v_f_312_, v_init_313_);
return v___x_321_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_le(v___x_319_, v___x_319_);
if (v___x_322_ == 0)
{
if (v___x_320_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_316_, v_f_312_, v_init_313_);
return v___x_323_;
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_319_);
lean_inc(v_f_312_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_312_, v_buckets_317_, v___x_324_, v___x_325_, v_init_313_);
v___x_327_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_316_, v_f_312_, v___x_326_);
return v___x_327_;
}
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_319_);
lean_inc(v_f_312_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_312_, v_buckets_317_, v___x_328_, v___x_329_, v_init_313_);
v___x_331_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_316_, v_f_312_, v___x_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_332_, lean_object* v_init_333_, lean_object* v_m_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v_f_332_, v_init_333_, v_m_334_);
lean_dec_ref(v_m_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___lam__0(lean_object* v_es_336_, lean_object* v_a_337_, lean_object* v_b_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_a_337_);
lean_ctor_set(v___x_339_, 1, v_b_338_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_es_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(lean_object* v_m_342_){
_start:
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___f_343_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0));
v___x_344_ = lean_box(0);
v___x_345_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v___f_343_, v___x_344_, v_m_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___boxed(lean_object* v_m_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(v_m_346_);
lean_dec_ref(v_m_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11_spec__16(lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_dec(v_x_348_);
return v_x_349_;
}
else
{
lean_object* v_head_351_; lean_object* v_tail_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
v_head_351_ = lean_ctor_get(v_x_350_, 0);
v_tail_352_ = lean_ctor_get(v_x_350_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_362_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_tail_352_);
lean_inc(v_head_351_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
lean_inc(v_x_348_);
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 5);
lean_ctor_set(v___x_354_, 1, v_x_348_);
lean_ctor_set(v___x_354_, 0, v_x_349_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_x_349_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_x_348_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_351_);
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v_x_349_ = v___x_359_;
v_x_350_ = v_tail_352_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11(lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_dec(v_x_363_);
return v_x_364_;
}
else
{
lean_object* v_head_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_head_366_ = lean_ctor_get(v_x_365_, 0);
v_tail_367_ = lean_ctor_get(v_x_365_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v_x_365_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_head_366_);
lean_dec(v_x_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
lean_inc(v_x_363_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 5);
lean_ctor_set(v___x_369_, 1, v_x_363_);
lean_ctor_set(v___x_369_, 0, v_x_364_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_x_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_x_363_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_366_);
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11_spec__16(v_x_363_, v___x_374_, v_tail_367_);
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v___x_380_; 
lean_dec(v_x_379_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v_tail_381_; 
v_tail_381_ = lean_ctor_get(v_x_378_, 1);
if (lean_obj_tag(v_tail_381_) == 0)
{
lean_object* v_head_382_; lean_object* v___x_383_; 
lean_dec(v_x_379_);
v_head_382_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_head_382_);
lean_dec_ref_known(v_x_378_, 2);
v___x_383_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_382_);
return v___x_383_;
}
else
{
lean_object* v_head_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc(v_tail_381_);
v_head_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_head_384_);
lean_dec_ref_known(v_x_378_, 2);
v___x_385_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_384_);
v___x_386_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11(v_x_379_, v___x_385_, v_tail_381_);
return v___x_386_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2));
v___x_392_ = lean_string_length(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_394_ = lean_nat_to_int(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(lean_object* v_a_397_){
_start:
{
if (lean_obj_tag(v_a_397_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1));
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; 
v___x_399_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3));
v___x_400_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8(v_a_397_, v___x_399_);
v___x_401_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4);
v___x_402_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_400_);
v___x_404_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8));
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_401_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = 0;
v___x_408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7_spec__10(lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_dec(v_x_409_);
return v_x_410_;
}
else
{
lean_object* v_head_412_; lean_object* v_tail_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_422_; 
v_head_412_ = lean_ctor_get(v_x_411_, 0);
v_tail_413_ = lean_ctor_get(v_x_411_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_411_);
if (v_isSharedCheck_422_ == 0)
{
v___x_415_ = v_x_411_;
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tail_413_);
lean_inc(v_head_412_);
lean_dec(v_x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
lean_inc(v_x_409_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 5);
lean_ctor_set(v___x_415_, 1, v_x_409_);
lean_ctor_set(v___x_415_, 0, v_x_410_);
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_x_410_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_x_409_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_head_412_);
v_x_410_ = v___x_419_;
v_x_411_ = v_tail_413_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v___x_425_; 
lean_dec(v_x_424_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v_tail_426_; 
v_tail_426_ = lean_ctor_get(v_x_423_, 1);
if (lean_obj_tag(v_tail_426_) == 0)
{
lean_object* v_head_427_; 
lean_dec(v_x_424_);
v_head_427_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_head_427_);
lean_dec_ref_known(v_x_423_, 2);
return v_head_427_;
}
else
{
lean_object* v_head_428_; lean_object* v___x_429_; 
lean_inc(v_tail_426_);
v_head_428_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_head_428_);
lean_dec_ref_known(v_x_423_, 2);
v___x_429_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7_spec__10(v_x_424_, v_head_428_, v_tail_426_);
return v___x_429_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0));
v___x_433_ = lean_string_length(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2);
v___x_435_ = lean_nat_to_int(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(lean_object* v_x_440_){
_start:
{
lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_465_; 
v_fst_441_ = lean_ctor_get(v_x_440_, 0);
v_snd_442_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_465_ == 0)
{
v___x_444_ = v_x_440_;
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snd_442_);
lean_inc(v_fst_441_);
lean_dec(v_x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Lean_Name_reprPrec(v_fst_441_, v___x_446_);
v___x_448_ = lean_box(0);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 1, v___x_448_);
lean_ctor_set(v___x_444_, 0, v___x_447_);
v___x_450_ = v___x_444_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_464_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; 
v___x_451_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(v_snd_442_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
v___x_453_ = l_List_reverse___redArg(v___x_452_);
v___x_454_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3));
v___x_455_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7(v___x_453_, v___x_454_);
v___x_456_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3);
v___x_457_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4));
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_455_);
v___x_459_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5));
v___x_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_456_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = 0;
v___x_463_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*1, v___x_462_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9_spec__13(lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_dec(v_x_466_);
return v_x_467_;
}
else
{
lean_object* v_head_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
v_head_469_ = lean_ctor_get(v_x_468_, 0);
v_tail_470_ = lean_ctor_get(v_x_468_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_480_ == 0)
{
v___x_472_ = v_x_468_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_head_469_);
lean_dec(v_x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
lean_inc(v_x_466_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 5);
lean_ctor_set(v___x_472_, 1, v_x_466_);
lean_ctor_set(v___x_472_, 0, v_x_467_);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_x_466_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_469_);
v___x_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v_x_467_ = v___x_477_;
v_x_468_ = v_tail_470_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_dec(v_x_481_);
return v_x_482_;
}
else
{
lean_object* v_head_484_; lean_object* v_tail_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_495_; 
v_head_484_ = lean_ctor_get(v_x_483_, 0);
v_tail_485_ = lean_ctor_get(v_x_483_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_495_ == 0)
{
v___x_487_ = v_x_483_;
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_tail_485_);
lean_inc(v_head_484_);
lean_dec(v_x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
lean_inc(v_x_481_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 5);
lean_ctor_set(v___x_487_, 1, v_x_481_);
lean_ctor_set(v___x_487_, 0, v_x_482_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_x_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_x_481_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_484_);
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9_spec__13(v_x_481_, v___x_492_, v_tail_485_);
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_498_; 
lean_dec(v_x_497_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v_tail_499_; 
v_tail_499_ = lean_ctor_get(v_x_496_, 1);
if (lean_obj_tag(v_tail_499_) == 0)
{
lean_object* v_head_500_; lean_object* v___x_501_; 
lean_dec(v_x_497_);
v_head_500_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_head_500_);
lean_dec_ref_known(v_x_496_, 2);
v___x_501_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_500_);
return v___x_501_;
}
else
{
lean_object* v_head_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_tail_499_);
v_head_502_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_head_502_);
lean_dec_ref_known(v_x_496_, 2);
v___x_503_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_502_);
v___x_504_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9(v_x_497_, v___x_503_, v_tail_499_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(lean_object* v_a_505_){
_start:
{
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1));
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_507_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3));
v___x_508_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3(v_a_505_, v___x_507_);
v___x_509_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4);
v___x_510_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_508_);
v___x_512_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8));
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_509_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = 0;
v___x_516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*1, v___x_515_);
return v___x_516_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(10u);
v___x_527_ = lean_nat_to_int(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3));
v___x_533_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4, &l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(v_x_531_);
v___x_536_ = l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6));
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v___x_534_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_533_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_532_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_obj_once(&l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19, &l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19);
v___x_545_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20));
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_543_);
v___x_547_ = ((lean_object*)(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21));
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_544_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_541_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___boxed(lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(v_x_551_);
lean_dec_ref(v_x_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr(lean_object* v_x_553_, lean_object* v_prec_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(v_x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprSimpCongrTheorems_repr___boxed(lean_object* v_x_556_, lean_object* v_prec_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_instReprSimpCongrTheorems_repr(v_x_556_, v_prec_557_);
lean_dec(v_prec_557_);
lean_dec_ref(v_x_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0(lean_object* v_00_u03b2_559_, lean_object* v_m_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(v_m_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___boxed(lean_object* v_00_u03b2_562_, lean_object* v_m_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0(v_00_u03b2_562_, v_m_563_);
lean_dec_ref(v_m_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1(lean_object* v_a_565_, lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(v_a_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___boxed(lean_object* v_a_568_, lean_object* v_n_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1(v_a_568_, v_n_569_);
lean_dec(v_n_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_00_u03c3_572_, lean_object* v_f_573_, lean_object* v_init_574_, lean_object* v_m_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v_f_573_, v_init_574_, v_m_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_577_, lean_object* v_00_u03c3_578_, lean_object* v_f_579_, lean_object* v_init_580_, lean_object* v_m_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0(v_00_u03b2_577_, v_00_u03c3_578_, v_f_579_, v_init_580_, v_m_581_);
lean_dec_ref(v_m_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_x_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___boxed(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2(v_x_586_, v_x_587_);
lean_dec(v_x_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_589_, lean_object* v_00_u03c3_590_, lean_object* v_f_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(v_f_591_, v_x_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_595_, lean_object* v_00_u03b2_596_, lean_object* v_map_597_, lean_object* v_f_598_, lean_object* v_init_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_597_, v_f_598_, v_init_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_601_, lean_object* v_00_u03b2_602_, lean_object* v_map_603_, lean_object* v_f_604_, lean_object* v_init_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2(v_00_u03c3_601_, v_00_u03b2_602_, v_map_603_, v_f_604_, v_init_605_);
lean_dec_ref(v_map_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_607_, lean_object* v_00_u03c3_608_, lean_object* v_f_609_, lean_object* v_as_610_, size_t v_i_611_, size_t v_stop_612_, lean_object* v_b_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_609_, v_as_610_, v_i_611_, v_stop_612_, v_b_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_615_, lean_object* v_00_u03c3_616_, lean_object* v_f_617_, lean_object* v_as_618_, lean_object* v_i_619_, lean_object* v_stop_620_, lean_object* v_b_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; lean_object* v_res_624_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_620_);
lean_dec(v_stop_620_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3(v_00_u03b2_615_, v_00_u03c3_616_, v_f_617_, v_as_618_, v_i_boxed_622_, v_stop_boxed_623_, v_b_621_);
lean_dec_ref(v_as_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6(lean_object* v_a_625_, lean_object* v_n_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(v_a_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___boxed(lean_object* v_a_628_, lean_object* v_n_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6(v_a_628_, v_n_629_);
lean_dec(v_n_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_map_631_, lean_object* v_f_632_, lean_object* v_init_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_632_, v_map_631_, v_init_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_map_635_, lean_object* v_f_636_, lean_object* v_init_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_635_, v_f_636_, v_init_637_);
lean_dec_ref(v_map_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03c3_639_, lean_object* v_00_u03b2_640_, lean_object* v_map_641_, lean_object* v_f_642_, lean_object* v_init_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_642_, v_map_641_, v_init_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03c3_645_, lean_object* v_00_u03b2_646_, lean_object* v_map_647_, lean_object* v_f_648_, lean_object* v_init_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_645_, v_00_u03b2_646_, v_map_647_, v_f_648_, v_init_649_);
lean_dec_ref(v_map_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_651_, lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_f_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_658_, lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_f_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_658_, v_00_u03b1_659_, v_00_u03b2_660_, v_f_661_, v_x_662_, v_x_663_);
lean_dec_ref(v_x_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_00_u03c3_667_, lean_object* v_f_668_, lean_object* v_as_669_, size_t v_i_670_, size_t v_stop_671_, lean_object* v_b_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_668_, v_as_669_, v_i_670_, v_stop_671_, v_b_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_00_u03c3_676_, lean_object* v_f_677_, lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_stop_680_, lean_object* v_b_681_){
_start:
{
size_t v_i_boxed_682_; size_t v_stop_boxed_683_; lean_object* v_res_684_; 
v_i_boxed_682_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_stop_boxed_683_ = lean_unbox_usize(v_stop_680_);
lean_dec(v_stop_680_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_674_, v_00_u03b2_675_, v_00_u03c3_676_, v_f_677_, v_as_678_, v_i_boxed_682_, v_stop_boxed_683_, v_b_681_);
lean_dec_ref(v_as_678_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object* v_00_u03c3_685_, lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_f_688_, lean_object* v_keys_689_, lean_object* v_vals_690_, lean_object* v_heq_691_, lean_object* v_i_692_, lean_object* v_acc_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_688_, v_keys_689_, v_vals_690_, v_i_692_, v_acc_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object* v_00_u03c3_695_, lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_f_698_, lean_object* v_keys_699_, lean_object* v_vals_700_, lean_object* v_heq_701_, lean_object* v_i_702_, lean_object* v_acc_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_695_, v_00_u03b1_696_, v_00_u03b2_697_, v_f_698_, v_keys_699_, v_vals_700_, v_heq_701_, v_i_702_, v_acc_703_);
lean_dec_ref(v_vals_700_);
lean_dec_ref(v_keys_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(lean_object* v_a_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
lean_object* v_key_710_; lean_object* v_value_711_; lean_object* v_tail_712_; uint8_t v___x_713_; 
v_key_710_ = lean_ctor_get(v_x_708_, 0);
v_value_711_ = lean_ctor_get(v_x_708_, 1);
v_tail_712_ = lean_ctor_get(v_x_708_, 2);
v___x_713_ = lean_name_eq(v_key_710_, v_a_707_);
if (v___x_713_ == 0)
{
v_x_708_ = v_tail_712_;
goto _start;
}
else
{
lean_object* v___x_715_; 
lean_inc(v_value_711_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_value_711_);
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_716_, v_x_717_);
lean_dec(v_x_717_);
lean_dec(v_a_716_);
return v_res_718_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_719_; uint64_t v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(1723u);
v___x_720_ = lean_uint64_of_nat(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_buckets_723_; lean_object* v___x_724_; uint64_t v___y_726_; 
v_buckets_723_ = lean_ctor_get(v_m_721_, 1);
v___x_724_ = lean_array_get_size(v_buckets_723_);
if (lean_obj_tag(v_a_722_) == 0)
{
uint64_t v___x_740_; 
v___x_740_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_726_ = v___x_740_;
goto v___jp_725_;
}
else
{
uint64_t v_hash_741_; 
v_hash_741_ = lean_ctor_get_uint64(v_a_722_, sizeof(void*)*2);
v___y_726_ = v_hash_741_;
goto v___jp_725_;
}
v___jp_725_:
{
uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_fold_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_727_ = 32ULL;
v___x_728_ = lean_uint64_shift_right(v___y_726_, v___x_727_);
v_fold_729_ = lean_uint64_xor(v___y_726_, v___x_728_);
v___x_730_ = 16ULL;
v___x_731_ = lean_uint64_shift_right(v_fold_729_, v___x_730_);
v___x_732_ = lean_uint64_xor(v_fold_729_, v___x_731_);
v___x_733_ = lean_uint64_to_usize(v___x_732_);
v___x_734_ = lean_usize_of_nat(v___x_724_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_sub(v___x_734_, v___x_735_);
v___x_737_ = lean_usize_land(v___x_733_, v___x_736_);
v___x_738_ = lean_array_uget_borrowed(v_buckets_723_, v___x_737_);
v___x_739_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_722_, v___x_738_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___boxed(lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_m_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_m_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_745_, lean_object* v_vals_746_, lean_object* v_i_747_, lean_object* v_k_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_keys_745_);
v___x_750_ = lean_nat_dec_lt(v_i_747_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v_i_747_);
v___x_751_ = lean_box(0);
return v___x_751_;
}
else
{
lean_object* v_k_x27_752_; uint8_t v___x_753_; 
v_k_x27_752_ = lean_array_fget_borrowed(v_keys_745_, v_i_747_);
v___x_753_ = lean_name_eq(v_k_748_, v_k_x27_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_i_747_, v___x_754_);
lean_dec(v_i_747_);
v_i_747_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_array_fget_borrowed(v_vals_746_, v_i_747_);
lean_dec(v_i_747_);
lean_inc(v___x_757_);
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_759_, lean_object* v_vals_760_, lean_object* v_i_761_, lean_object* v_k_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_759_, v_vals_760_, v_i_761_, v_k_762_);
lean_dec(v_k_762_);
lean_dec_ref(v_vals_760_);
lean_dec_ref(v_keys_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(lean_object* v_x_764_, size_t v_x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v_es_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v_j_771_; lean_object* v___x_772_; 
v_es_767_ = lean_ctor_get(v_x_764_, 0);
v___x_768_ = lean_box(2);
v___x_769_ = ((size_t)31ULL);
v___x_770_ = lean_usize_land(v_x_765_, v___x_769_);
v_j_771_ = lean_usize_to_nat(v___x_770_);
v___x_772_ = lean_array_get_borrowed(v___x_768_, v_es_767_, v_j_771_);
lean_dec(v_j_771_);
switch(lean_obj_tag(v___x_772_))
{
case 0:
{
lean_object* v_key_773_; lean_object* v_val_774_; uint8_t v___x_775_; 
v_key_773_ = lean_ctor_get(v___x_772_, 0);
v_val_774_ = lean_ctor_get(v___x_772_, 1);
v___x_775_ = lean_name_eq(v_x_766_, v_key_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
lean_object* v___x_777_; 
lean_inc(v_val_774_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_val_774_);
return v___x_777_;
}
}
case 1:
{
lean_object* v_node_778_; size_t v___x_779_; size_t v___x_780_; 
v_node_778_ = lean_ctor_get(v___x_772_, 0);
v___x_779_ = ((size_t)5ULL);
v___x_780_ = lean_usize_shift_right(v_x_765_, v___x_779_);
v_x_764_ = v_node_778_;
v_x_765_ = v___x_780_;
goto _start;
}
default: 
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v_vs_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_ks_783_ = lean_ctor_get(v_x_764_, 0);
v_vs_784_ = lean_ctor_get(v_x_764_, 1);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_783_, v_vs_784_, v___x_785_, v_x_766_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
size_t v_x_321__boxed_790_; lean_object* v_res_791_; 
v_x_321__boxed_790_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_787_, v_x_321__boxed_790_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_x_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint64_t v___y_795_; 
if (lean_obj_tag(v_x_793_) == 0)
{
uint64_t v___x_798_; 
v___x_798_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_795_ = v___x_798_;
goto v___jp_794_;
}
else
{
uint64_t v_hash_799_; 
v_hash_799_ = lean_ctor_get_uint64(v_x_793_, sizeof(void*)*2);
v___y_795_ = v_hash_799_;
goto v___jp_794_;
}
v___jp_794_:
{
size_t v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_uint64_to_usize(v___y_795_);
v___x_797_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_792_, v___x_796_, v_x_793_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg___boxed(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_800_, v_x_801_);
lean_dec(v_x_801_);
lean_dec_ref(v_x_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
uint8_t v_stage_u2081_805_; 
v_stage_u2081_805_ = lean_ctor_get_uint8(v_x_803_, sizeof(void*)*2);
if (v_stage_u2081_805_ == 0)
{
lean_object* v_map_u2081_806_; lean_object* v_map_u2082_807_; lean_object* v___x_808_; 
v_map_u2081_806_ = lean_ctor_get(v_x_803_, 0);
v_map_u2082_807_ = lean_ctor_get(v_x_803_, 1);
v___x_808_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_map_u2082_807_, v_x_804_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_806_, v_x_804_);
return v___x_809_;
}
else
{
return v___x_808_;
}
}
else
{
lean_object* v_map_u2081_810_; lean_object* v___x_811_; 
v_map_u2081_810_ = lean_ctor_get(v_x_803_, 0);
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_810_, v_x_804_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg___boxed(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_x_812_, v_x_813_);
lean_dec(v_x_813_);
lean_dec_ref(v_x_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get(lean_object* v_d_815_, lean_object* v_declName_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_d_815_, v_declName_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v_val_819_; 
v_val_819_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_817_, 1);
return v_val_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get___boxed(lean_object* v_d_820_, lean_object* v_declName_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Meta_SimpCongrTheorems_get(v_d_820_, v_declName_821_);
lean_dec(v_declName_821_);
lean_dec_ref(v_d_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_x_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___boxed(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(v_00_u03b2_827_, v_x_828_, v_x_829_);
lean_dec(v_x_829_);
lean_dec_ref(v_x_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___boxed(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(v_00_u03b2_835_, v_x_836_, v_x_837_);
lean_dec(v_x_837_);
lean_dec_ref(v_x_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_m_840_, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___boxed(lean_object* v_00_u03b2_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(v_00_u03b2_843_, v_m_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, size_t v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
size_t v_x_432__boxed_856_; lean_object* v_res_857_; 
v_x_432__boxed_856_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_res_857_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(v_00_u03b2_852_, v_x_853_, v_x_432__boxed_856_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_x_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_858_, lean_object* v_a_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_862_, lean_object* v_a_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(v_00_u03b2_862_, v_a_863_, v_x_864_);
lean_dec(v_x_864_);
lean_dec(v_a_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_866_, lean_object* v_keys_867_, lean_object* v_vals_868_, lean_object* v_heq_869_, lean_object* v_i_870_, lean_object* v_k_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_867_, v_vals_868_, v_i_870_, v_k_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_heq_876_, lean_object* v_i_877_, lean_object* v_k_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_873_, v_keys_874_, v_vals_875_, v_heq_876_, v_i_877_, v_k_878_);
lean_dec(v_k_878_);
lean_dec_ref(v_vals_875_);
lean_dec_ref(v_keys_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(lean_object* v_e_880_, lean_object* v_a_881_){
_start:
{
if (lean_obj_tag(v_a_881_) == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v_e_880_);
lean_ctor_set(v___x_882_, 1, v_a_881_);
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v_priority_885_; lean_object* v_priority_886_; uint8_t v___x_887_; 
v_head_883_ = lean_ctor_get(v_a_881_, 0);
v_tail_884_ = lean_ctor_get(v_a_881_, 1);
v_priority_885_ = lean_ctor_get(v_head_883_, 3);
v_priority_886_ = lean_ctor_get(v_e_880_, 3);
v___x_887_ = lean_nat_dec_le(v_priority_885_, v_priority_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
lean_inc(v_tail_884_);
lean_inc(v_head_883_);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; lean_object* v_unused_897_; 
v_unused_896_ = lean_ctor_get(v_a_881_, 1);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_a_881_, 0);
lean_dec(v_unused_897_);
v___x_889_ = v_a_881_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_a_881_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_880_, v_tail_884_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_head_883_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v_e_880_);
lean_ctor_set(v___x_898_, 1, v_a_881_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec(v_b_900_);
lean_dec(v_a_899_);
return v_x_901_;
}
else
{
lean_object* v_key_902_; lean_object* v_value_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_916_; 
v_key_902_ = lean_ctor_get(v_x_901_, 0);
v_value_903_ = lean_ctor_get(v_x_901_, 1);
v_tail_904_ = lean_ctor_get(v_x_901_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_916_ == 0)
{
v___x_906_ = v_x_901_;
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_value_903_);
lean_inc(v_key_902_);
lean_dec(v_x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___x_908_; 
v___x_908_ = lean_name_eq(v_key_902_, v_a_899_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_899_, v_b_900_, v_tail_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_key_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_value_903_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v_value_903_);
lean_dec(v_key_902_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_b_900_);
lean_ctor_set(v___x_906_, 0, v_a_899_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_899_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_b_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_tail_904_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
return v_x_917_;
}
else
{
lean_object* v_key_919_; lean_object* v_value_920_; lean_object* v_tail_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_947_; 
v_key_919_ = lean_ctor_get(v_x_918_, 0);
v_value_920_ = lean_ctor_get(v_x_918_, 1);
v_tail_921_ = lean_ctor_get(v_x_918_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_947_ == 0)
{
v___x_923_ = v_x_918_;
v_isShared_924_ = v_isSharedCheck_947_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_tail_921_);
lean_inc(v_value_920_);
lean_inc(v_key_919_);
lean_dec(v_x_918_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_947_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; uint64_t v___y_927_; 
v___x_925_ = lean_array_get_size(v_x_917_);
if (lean_obj_tag(v_key_919_) == 0)
{
uint64_t v___x_945_; 
v___x_945_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_927_ = v___x_945_;
goto v___jp_926_;
}
else
{
uint64_t v_hash_946_; 
v_hash_946_ = lean_ctor_get_uint64(v_key_919_, sizeof(void*)*2);
v___y_927_ = v_hash_946_;
goto v___jp_926_;
}
v___jp_926_:
{
uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v_fold_930_; uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; size_t v___x_934_; size_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_928_ = 32ULL;
v___x_929_ = lean_uint64_shift_right(v___y_927_, v___x_928_);
v_fold_930_ = lean_uint64_xor(v___y_927_, v___x_929_);
v___x_931_ = 16ULL;
v___x_932_ = lean_uint64_shift_right(v_fold_930_, v___x_931_);
v___x_933_ = lean_uint64_xor(v_fold_930_, v___x_932_);
v___x_934_ = lean_uint64_to_usize(v___x_933_);
v___x_935_ = lean_usize_of_nat(v___x_925_);
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_sub(v___x_935_, v___x_936_);
v___x_938_ = lean_usize_land(v___x_934_, v___x_937_);
v___x_939_ = lean_array_uget_borrowed(v_x_917_, v___x_938_);
lean_inc(v___x_939_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 2, v___x_939_);
v___x_941_ = v___x_923_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_key_919_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_value_920_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v___x_939_);
v___x_941_ = v_reuseFailAlloc_944_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; 
v___x_942_ = lean_array_uset(v_x_917_, v___x_938_, v___x_941_);
v_x_917_ = v___x_942_;
v_x_918_ = v_tail_921_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_948_, lean_object* v_source_949_, lean_object* v_target_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_get_size(v_source_949_);
v___x_952_ = lean_nat_dec_lt(v_i_948_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec_ref(v_source_949_);
lean_dec(v_i_948_);
return v_target_950_;
}
else
{
lean_object* v_es_953_; lean_object* v___x_954_; lean_object* v_source_955_; lean_object* v_target_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_es_953_ = lean_array_fget(v_source_949_, v_i_948_);
v___x_954_ = lean_box(0);
v_source_955_ = lean_array_fset(v_source_949_, v_i_948_, v___x_954_);
v_target_956_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_950_, v_es_953_);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_i_948_, v___x_957_);
lean_dec(v_i_948_);
v_i_948_ = v___x_958_;
v_source_949_ = v_source_955_;
v_target_950_ = v_target_956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_data_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_nbuckets_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_961_ = lean_array_get_size(v_data_960_);
v___x_962_ = lean_unsigned_to_nat(2u);
v_nbuckets_963_ = lean_nat_mul(v___x_961_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_box(0);
v___x_966_ = lean_mk_array(v_nbuckets_963_, v___x_965_);
v___x_967_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_964_, v_data_960_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_968_, lean_object* v_x_969_){
_start:
{
if (lean_obj_tag(v_x_969_) == 0)
{
uint8_t v___x_970_; 
v___x_970_ = 0;
return v___x_970_;
}
else
{
lean_object* v_key_971_; lean_object* v_tail_972_; uint8_t v___x_973_; 
v_key_971_ = lean_ctor_get(v_x_969_, 0);
v_tail_972_ = lean_ctor_get(v_x_969_, 2);
v___x_973_ = lean_name_eq(v_key_971_, v_a_968_);
if (v___x_973_ == 0)
{
v_x_969_ = v_tail_972_;
goto _start;
}
else
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec(v_a_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(lean_object* v_m_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_size_982_; lean_object* v_buckets_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1029_; 
v_size_982_ = lean_ctor_get(v_m_979_, 0);
v_buckets_983_ = lean_ctor_get(v_m_979_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_m_979_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_985_ = v_m_979_;
v_isShared_986_ = v_isSharedCheck_1029_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_buckets_983_);
lean_inc(v_size_982_);
lean_dec(v_m_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1029_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; uint64_t v___y_989_; 
v___x_987_ = lean_array_get_size(v_buckets_983_);
if (lean_obj_tag(v_a_980_) == 0)
{
uint64_t v___x_1027_; 
v___x_1027_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_989_ = v___x_1027_;
goto v___jp_988_;
}
else
{
uint64_t v_hash_1028_; 
v_hash_1028_ = lean_ctor_get_uint64(v_a_980_, sizeof(void*)*2);
v___y_989_ = v_hash_1028_;
goto v___jp_988_;
}
v___jp_988_:
{
uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v_fold_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v_bkt_1001_; uint8_t v___x_1002_; 
v___x_990_ = 32ULL;
v___x_991_ = lean_uint64_shift_right(v___y_989_, v___x_990_);
v_fold_992_ = lean_uint64_xor(v___y_989_, v___x_991_);
v___x_993_ = 16ULL;
v___x_994_ = lean_uint64_shift_right(v_fold_992_, v___x_993_);
v___x_995_ = lean_uint64_xor(v_fold_992_, v___x_994_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = lean_usize_of_nat(v___x_987_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_sub(v___x_997_, v___x_998_);
v___x_1000_ = lean_usize_land(v___x_996_, v___x_999_);
v_bkt_1001_ = lean_array_uget_borrowed(v_buckets_983_, v___x_1000_);
v___x_1002_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_980_, v_bkt_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v_size_x27_1004_; lean_object* v___x_1005_; lean_object* v_buckets_x27_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v_size_x27_1004_ = lean_nat_add(v_size_982_, v___x_1003_);
lean_dec(v_size_982_);
lean_inc(v_bkt_1001_);
v___x_1005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_a_980_);
lean_ctor_set(v___x_1005_, 1, v_b_981_);
lean_ctor_set(v___x_1005_, 2, v_bkt_1001_);
v_buckets_x27_1006_ = lean_array_uset(v_buckets_983_, v___x_1000_, v___x_1005_);
v___x_1007_ = lean_unsigned_to_nat(4u);
v___x_1008_ = lean_nat_mul(v_size_x27_1004_, v___x_1007_);
v___x_1009_ = lean_unsigned_to_nat(3u);
v___x_1010_ = lean_nat_div(v___x_1008_, v___x_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_array_get_size(v_buckets_x27_1006_);
v___x_1012_ = lean_nat_dec_le(v___x_1010_, v___x_1011_);
lean_dec(v___x_1010_);
if (v___x_1012_ == 0)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; 
v_val_1013_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1006_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_val_1013_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1004_);
v___x_1015_ = v___x_985_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_size_x27_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_val_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1018_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_buckets_x27_1006_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1004_);
v___x_1018_ = v___x_985_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_size_x27_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_buckets_x27_1006_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v_buckets_x27_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_inc(v_bkt_1001_);
v___x_1020_ = lean_box(0);
v_buckets_x27_1021_ = lean_array_uset(v_buckets_983_, v___x_1000_, v___x_1020_);
v___x_1022_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_980_, v_b_981_, v_bkt_1001_);
v___x_1023_ = lean_array_uset(v_buckets_x27_1021_, v___x_1000_, v___x_1022_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_1023_);
v___x_1025_ = v___x_985_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_size_982_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v_ks_1034_; lean_object* v_vs_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1059_; 
v_ks_1034_ = lean_ctor_get(v_x_1030_, 0);
v_vs_1035_ = lean_ctor_get(v_x_1030_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1037_ = v_x_1030_;
v_isShared_1038_ = v_isSharedCheck_1059_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_vs_1035_);
lean_inc(v_ks_1034_);
lean_dec(v_x_1030_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1059_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_array_get_size(v_ks_1034_);
v___x_1040_ = lean_nat_dec_lt(v_x_1031_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_x_1031_);
v___x_1041_ = lean_array_push(v_ks_1034_, v_x_1032_);
v___x_1042_ = lean_array_push(v_vs_1035_, v_x_1033_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1042_);
lean_ctor_set(v___x_1037_, 0, v___x_1041_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v_k_x27_1046_; uint8_t v___x_1047_; 
v_k_x27_1046_ = lean_array_fget_borrowed(v_ks_1034_, v_x_1031_);
v___x_1047_ = lean_name_eq(v_x_1032_, v_k_x27_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1049_; 
if (v_isShared_1038_ == 0)
{
v___x_1049_ = v___x_1037_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_ks_1034_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_vs_1035_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_x_1031_, v___x_1050_);
lean_dec(v_x_1031_);
v_x_1030_ = v___x_1049_;
v_x_1031_ = v___x_1051_;
goto _start;
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_array_fset(v_ks_1034_, v_x_1031_, v_x_1032_);
v___x_1055_ = lean_array_fset(v_vs_1035_, v_x_1031_, v_x_1033_);
lean_dec(v_x_1031_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1055_);
lean_ctor_set(v___x_1037_, 0, v___x_1054_);
v___x_1057_ = v___x_1037_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_1060_, v___x_1063_, v_k_1061_, v_v_1062_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1066_, size_t v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v_es_1071_; size_t v___x_1072_; size_t v___x_1073_; lean_object* v_j_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_es_1071_ = lean_ctor_get(v_x_1066_, 0);
v___x_1072_ = ((size_t)31ULL);
v___x_1073_ = lean_usize_land(v_x_1067_, v___x_1072_);
v_j_1074_ = lean_usize_to_nat(v___x_1073_);
v___x_1075_ = lean_array_get_size(v_es_1071_);
v___x_1076_ = lean_nat_dec_lt(v_j_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_j_1074_);
lean_dec(v_x_1070_);
lean_dec(v_x_1069_);
return v_x_1066_;
}
else
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1115_; 
lean_inc_ref(v_es_1071_);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_x_1066_, 0);
lean_dec(v_unused_1116_);
v___x_1078_ = v_x_1066_;
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v_x_1066_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_v_1080_; lean_object* v___x_1081_; lean_object* v_xs_x27_1082_; lean_object* v___y_1084_; 
v_v_1080_ = lean_array_fget(v_es_1071_, v_j_1074_);
v___x_1081_ = lean_box(0);
v_xs_x27_1082_ = lean_array_fset(v_es_1071_, v_j_1074_, v___x_1081_);
switch(lean_obj_tag(v_v_1080_))
{
case 0:
{
lean_object* v_key_1089_; lean_object* v_val_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_key_1089_ = lean_ctor_get(v_v_1080_, 0);
v_val_1090_ = lean_ctor_get(v_v_1080_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_v_1080_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v_v_1080_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_val_1090_);
lean_inc(v_key_1089_);
lean_dec(v_v_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_name_eq(v_x_1069_, v_key_1089_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_del_object(v___x_1092_);
v___x_1095_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1089_, v_val_1090_, v_x_1069_, v_x_1070_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___y_1084_ = v___x_1096_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_val_1090_);
lean_dec(v_key_1089_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v_x_1070_);
lean_ctor_set(v___x_1092_, 0, v_x_1069_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_x_1069_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_x_1070_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v___y_1084_ = v___x_1098_;
goto v___jp_1083_;
}
}
}
}
case 1:
{
lean_object* v_node_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1113_; 
v_node_1101_ = lean_ctor_get(v_v_1080_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_v_1080_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1103_ = v_v_1080_;
v_isShared_1104_ = v_isSharedCheck_1113_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_node_1101_);
lean_dec(v_v_1080_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1113_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1105_ = ((size_t)5ULL);
v___x_1106_ = lean_usize_shift_right(v_x_1067_, v___x_1105_);
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_add(v_x_1068_, v___x_1107_);
v___x_1109_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_node_1101_, v___x_1106_, v___x_1108_, v_x_1069_, v_x_1070_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1109_);
v___x_1111_ = v___x_1103_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v___y_1084_ = v___x_1111_;
goto v___jp_1083_;
}
}
}
default: 
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_x_1069_);
lean_ctor_set(v___x_1114_, 1, v_x_1070_);
v___y_1084_ = v___x_1114_;
goto v___jp_1083_;
}
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_array_fset(v_xs_x27_1082_, v_j_1074_, v___y_1084_);
lean_dec(v_j_1074_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1085_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v_ks_1117_; lean_object* v_vs_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1138_; 
v_ks_1117_ = lean_ctor_get(v_x_1066_, 0);
v_vs_1118_ = lean_ctor_get(v_x_1066_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1120_ = v_x_1066_;
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_vs_1118_);
lean_inc(v_ks_1117_);
lean_dec(v_x_1066_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_ks_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_vs_1118_);
v___x_1123_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v_newNode_1124_; uint8_t v___y_1126_; size_t v___x_1132_; uint8_t v___x_1133_; 
v_newNode_1124_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1123_, v_x_1069_, v_x_1070_);
v___x_1132_ = ((size_t)7ULL);
v___x_1133_ = lean_usize_dec_le(v___x_1132_, v_x_1068_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1124_);
v___x_1135_ = lean_unsigned_to_nat(4u);
v___x_1136_ = lean_nat_dec_lt(v___x_1134_, v___x_1135_);
lean_dec(v___x_1134_);
v___y_1126_ = v___x_1136_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___x_1133_;
goto v___jp_1125_;
}
v___jp_1125_:
{
if (v___y_1126_ == 0)
{
lean_object* v_ks_1127_; lean_object* v_vs_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_ks_1127_ = lean_ctor_get(v_newNode_1124_, 0);
lean_inc_ref(v_ks_1127_);
v_vs_1128_ = lean_ctor_get(v_newNode_1124_, 1);
lean_inc_ref(v_vs_1128_);
lean_dec_ref(v_newNode_1124_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1068_, v_ks_1127_, v_vs_1128_, v___x_1129_, v___x_1130_);
lean_dec_ref(v_vs_1128_);
lean_dec_ref(v_ks_1127_);
return v___x_1131_;
}
else
{
return v_newNode_1124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1139_, lean_object* v_keys_1140_, lean_object* v_vals_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_array_get_size(v_keys_1140_);
v___x_1145_ = lean_nat_dec_lt(v_i_1142_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v_i_1142_);
return v_entries_1143_;
}
else
{
lean_object* v_k_1146_; lean_object* v_v_1147_; uint64_t v___y_1149_; 
v_k_1146_ = lean_array_fget_borrowed(v_keys_1140_, v_i_1142_);
v_v_1147_ = lean_array_fget_borrowed(v_vals_1141_, v_i_1142_);
if (lean_obj_tag(v_k_1146_) == 0)
{
uint64_t v___x_1160_; 
v___x_1160_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_1149_ = v___x_1160_;
goto v___jp_1148_;
}
else
{
uint64_t v_hash_1161_; 
v_hash_1161_ = lean_ctor_get_uint64(v_k_1146_, sizeof(void*)*2);
v___y_1149_ = v_hash_1161_;
goto v___jp_1148_;
}
v___jp_1148_:
{
size_t v_h_1150_; size_t v___x_1151_; lean_object* v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v_h_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_h_1150_ = lean_uint64_to_usize(v___y_1149_);
v___x_1151_ = ((size_t)5ULL);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_sub(v_depth_1139_, v___x_1153_);
v___x_1155_ = lean_usize_mul(v___x_1151_, v___x_1154_);
v_h_1156_ = lean_usize_shift_right(v_h_1150_, v___x_1155_);
v___x_1157_ = lean_nat_add(v_i_1142_, v___x_1152_);
lean_dec(v_i_1142_);
lean_inc(v_v_1147_);
lean_inc(v_k_1146_);
v___x_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_entries_1143_, v_h_1156_, v_depth_1139_, v_k_1146_, v_v_1147_);
v_i_1142_ = v___x_1157_;
v_entries_1143_ = v___x_1158_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1162_, lean_object* v_keys_1163_, lean_object* v_vals_1164_, lean_object* v_i_1165_, lean_object* v_entries_1166_){
_start:
{
size_t v_depth_boxed_1167_; lean_object* v_res_1168_; 
v_depth_boxed_1167_ = lean_unbox_usize(v_depth_1162_);
lean_dec(v_depth_1162_);
v_res_1168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1167_, v_keys_1163_, v_vals_1164_, v_i_1165_, v_entries_1166_);
lean_dec_ref(v_vals_1164_);
lean_dec_ref(v_keys_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
size_t v_x_1048__boxed_1174_; size_t v_x_1049__boxed_1175_; lean_object* v_res_1176_; 
v_x_1048__boxed_1174_ = lean_unbox_usize(v_x_1170_);
lean_dec(v_x_1170_);
v_x_1049__boxed_1175_ = lean_unbox_usize(v_x_1171_);
lean_dec(v_x_1171_);
v_res_1176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1169_, v_x_1048__boxed_1174_, v_x_1049__boxed_1175_, v_x_1172_, v_x_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
uint64_t v___y_1181_; 
if (lean_obj_tag(v_x_1178_) == 0)
{
uint64_t v___x_1185_; 
v___x_1185_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_1181_ = v___x_1185_;
goto v___jp_1180_;
}
else
{
uint64_t v_hash_1186_; 
v_hash_1186_ = lean_ctor_get_uint64(v_x_1178_, sizeof(void*)*2);
v___y_1181_ = v_hash_1186_;
goto v___jp_1180_;
}
v___jp_1180_:
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_uint64_to_usize(v___y_1181_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1177_, v___x_1182_, v___x_1183_, v_x_1178_, v_x_1179_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v_stage_u2081_1190_; 
v_stage_u2081_1190_ = lean_ctor_get_uint8(v_x_1187_, sizeof(void*)*2);
if (v_stage_u2081_1190_ == 0)
{
lean_object* v_map_u2081_1191_; lean_object* v_map_u2082_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_map_u2081_1191_ = lean_ctor_get(v_x_1187_, 0);
v_map_u2082_1192_ = lean_ctor_get(v_x_1187_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v_x_1187_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_map_u2082_1192_);
lean_inc(v_map_u2081_1191_);
lean_dec(v_x_1187_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_map_u2082_1192_, v_x_1188_, v_x_1189_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_map_u2081_1191_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*2, v_stage_u2081_1190_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_map_u2081_1201_; lean_object* v_map_u2082_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
v_map_u2081_1201_ = lean_ctor_get(v_x_1187_, 0);
v_map_u2082_1202_ = lean_ctor_get(v_x_1187_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1204_ = v_x_1187_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_map_u2082_1202_);
lean_inc(v_map_u2081_1201_);
lean_dec(v_x_1187_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_map_u2081_1201_, v_x_1188_, v_x_1189_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_map_u2082_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2, v_stage_u2081_1190_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry(lean_object* v_d_1211_, lean_object* v_e_1212_){
_start:
{
lean_object* v_funName_1213_; lean_object* v___x_1214_; 
v_funName_1213_ = lean_ctor_get(v_e_1212_, 1);
lean_inc(v_funName_1213_);
v___x_1214_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_d_1211_, v_funName_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_e_1212_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_d_1211_, v_funName_1213_, v___x_1216_);
return v___x_1217_;
}
else
{
lean_object* v_val_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_val_1218_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1219_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_1212_, v_val_1218_);
v___x_1220_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_d_1211_, v_funName_1213_, v___x_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_x_1222_, v_x_1223_, v_x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0(lean_object* v_00_u03b2_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_x_1227_, v_x_1228_, v_x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1(lean_object* v_00_u03b2_1231_, lean_object* v_m_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_m_1232_, v_a_1233_, v_b_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1236_, lean_object* v_x_1237_, size_t v_x_1238_, size_t v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1237_, v_x_1238_, v_x_1239_, v_x_1240_, v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
size_t v_x_1307__boxed_1249_; size_t v_x_1308__boxed_1250_; lean_object* v_res_1251_; 
v_x_1307__boxed_1249_ = lean_unbox_usize(v_x_1245_);
lean_dec(v_x_1245_);
v_x_1308__boxed_1250_ = lean_unbox_usize(v_x_1246_);
lean_dec(v_x_1246_);
v_res_1251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(v_00_u03b2_1243_, v_x_1244_, v_x_1307__boxed_1249_, v_x_1308__boxed_1250_, v_x_1247_, v_x_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1252_, lean_object* v_a_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(v_00_u03b2_1256_, v_a_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec(v_a_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1261_, lean_object* v_data_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_data_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1264_, lean_object* v_a_1265_, lean_object* v_b_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_1265_, v_b_1266_, v_x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1269_, lean_object* v_n_1270_, lean_object* v_k_1271_, lean_object* v_v_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1270_, v_k_1271_, v_v_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1274_, size_t v_depth_1275_, lean_object* v_keys_1276_, lean_object* v_vals_1277_, lean_object* v_heq_1278_, lean_object* v_i_1279_, lean_object* v_entries_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1275_, v_keys_1276_, v_vals_1277_, v_i_1279_, v_entries_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1282_, lean_object* v_depth_1283_, lean_object* v_keys_1284_, lean_object* v_vals_1285_, lean_object* v_heq_1286_, lean_object* v_i_1287_, lean_object* v_entries_1288_){
_start:
{
size_t v_depth_boxed_1289_; lean_object* v_res_1290_; 
v_depth_boxed_1289_ = lean_unbox_usize(v_depth_1283_);
lean_dec(v_depth_1283_);
v_res_1290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1282_, v_depth_boxed_1289_, v_keys_1284_, v_vals_1285_, v_heq_1286_, v_i_1287_, v_entries_1288_);
lean_dec_ref(v_vals_1285_);
lean_dec_ref(v_keys_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1291_, lean_object* v_i_1292_, lean_object* v_source_1293_, lean_object* v_target_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_1292_, v_source_1293_, v_target_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1297_, v_x_1298_, v_x_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_1306_){
_start:
{
uint8_t v_stage_u2081_1307_; 
v_stage_u2081_1307_ = lean_ctor_get_uint8(v_m_1306_, sizeof(void*)*2);
if (v_stage_u2081_1307_ == 0)
{
return v_m_1306_;
}
else
{
lean_object* v_map_u2081_1308_; lean_object* v_map_u2082_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_map_u2081_1308_ = lean_ctor_get(v_m_1306_, 0);
v_map_u2082_1309_ = lean_ctor_get(v_m_1306_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_m_1306_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v_m_1306_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_map_u2082_1309_);
lean_inc(v_map_u2081_1308_);
lean_dec(v_m_1306_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
uint8_t v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = 0;
if (v_isShared_1312_ == 0)
{
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_map_u2081_1308_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_map_u2082_1309_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*2, v___x_1313_);
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1318_, lean_object* v_m_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(v_m_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(lean_object* v_x_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_a_1322_);
lean_inc_ref_n(v___x_1323_, 2);
v___x_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_ctor_set(v___x_1324_, 2, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object* v_x_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(v_x_1325_, v_a_1326_);
lean_dec_ref(v_x_1325_);
return v_res_1327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___f_1338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___f_1339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1340_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4);
v___x_1341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1340_);
lean_ctor_set(v___x_1343_, 3, v___f_1339_);
lean_ctor_set(v___x_1343_, 4, v___f_1338_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_);
v___x_1346_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
return v_res_1348_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(lean_object* v_k_1349_, lean_object* v_t_1350_){
_start:
{
if (lean_obj_tag(v_t_1350_) == 0)
{
lean_object* v_k_1351_; lean_object* v_l_1352_; lean_object* v_r_1353_; uint8_t v___x_1354_; 
v_k_1351_ = lean_ctor_get(v_t_1350_, 1);
v_l_1352_ = lean_ctor_get(v_t_1350_, 3);
v_r_1353_ = lean_ctor_get(v_t_1350_, 4);
v___x_1354_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1349_, v_k_1351_);
switch(v___x_1354_)
{
case 0:
{
v_t_1350_ = v_l_1352_;
goto _start;
}
case 1:
{
uint8_t v___x_1356_; 
v___x_1356_ = 1;
return v___x_1356_;
}
default: 
{
v_t_1350_ = v_r_1353_;
goto _start;
}
}
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg___boxed(lean_object* v_k_1359_, lean_object* v_t_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_1359_, v_t_1360_);
lean_dec(v_t_1360_);
lean_dec(v_k_1359_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(lean_object* v_mvarSet_1363_, lean_object* v_e_1364_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_Expr_isMVar(v_e_1364_);
if (v___x_1365_ == 0)
{
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; uint8_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = l_Lean_Expr_mvarId_x21(v_e_1364_);
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1366_, v_mvarSet_1363_);
lean_dec(v___x_1366_);
v___x_1368_ = lean_bool_not(v___x_1367_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(lean_object* v_mvarSet_1369_, lean_object* v_e_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(v_mvarSet_1369_, v_e_1370_);
lean_dec_ref(v_e_1370_);
lean_dec(v_mvarSet_1369_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(lean_object* v_t_1373_, lean_object* v_mvarSet_1374_){
_start:
{
lean_object* v___f_1375_; lean_object* v___x_1376_; 
v___f_1375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1375_, 0, v_mvarSet_1374_);
v___x_1376_ = lean_find_expr(v___f_1375_, v_t_1373_);
lean_dec_ref(v___f_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = 1;
return v___x_1377_;
}
else
{
uint8_t v___x_1378_; 
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = 0;
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(lean_object* v_t_1379_, lean_object* v_mvarSet_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_t_1379_, v_mvarSet_1380_);
lean_dec_ref(v_t_1379_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(lean_object* v_00_u03b2_1383_, lean_object* v_k_1384_, lean_object* v_t_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_1384_, v_t_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_k_1388_, lean_object* v_t_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(v_00_u03b2_1387_, v_k_1388_, v_t_1389_);
lean_dec(v_t_1389_);
lean_dec(v_k_1388_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(lean_object* v_k_1392_, lean_object* v_b_1393_, lean_object* v_c_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
v___x_1400_ = lean_apply_7(v_k_1392_, v_b_1393_, v_c_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, lean_box(0));
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed(lean_object* v_k_1401_, lean_object* v_b_1402_, lean_object* v_c_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(v_k_1401_, v_b_1402_, v_c_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(lean_object* v_type_1410_, lean_object* v_k_1411_, uint8_t v_cleanupAnnotations_1412_, uint8_t v_whnfType_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___f_1419_; lean_object* v___x_1420_; 
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1419_, 0, v_k_1411_);
v___x_1420_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1410_, v___f_1419_, v_cleanupAnnotations_1412_, v_whnfType_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_a_1429_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1420_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1420_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___boxed(lean_object* v_type_1437_, lean_object* v_k_1438_, lean_object* v_cleanupAnnotations_1439_, lean_object* v_whnfType_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1446_; uint8_t v_whnfType_boxed_1447_; lean_object* v_res_1448_; 
v_cleanupAnnotations_boxed_1446_ = lean_unbox(v_cleanupAnnotations_1439_);
v_whnfType_boxed_1447_ = lean_unbox(v_whnfType_1440_);
v_res_1448_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_type_1437_, v_k_1438_, v_cleanupAnnotations_boxed_1446_, v_whnfType_boxed_1447_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(lean_object* v_00_u03b1_1449_, lean_object* v_type_1450_, lean_object* v_k_1451_, uint8_t v_cleanupAnnotations_1452_, uint8_t v_whnfType_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_type_1450_, v_k_1451_, v_cleanupAnnotations_1452_, v_whnfType_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_type_1461_, lean_object* v_k_1462_, lean_object* v_cleanupAnnotations_1463_, lean_object* v_whnfType_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1470_; uint8_t v_whnfType_boxed_1471_; lean_object* v_res_1472_; 
v_cleanupAnnotations_boxed_1470_ = lean_unbox(v_cleanupAnnotations_1463_);
v_whnfType_boxed_1471_ = lean_unbox(v_whnfType_1464_);
v_res_1472_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(v_00_u03b1_1460_, v_type_1461_, v_k_1462_, v_cleanupAnnotations_boxed_1470_, v_whnfType_boxed_1471_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(lean_object* v_msgData_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v_env_1480_; lean_object* v___x_1481_; lean_object* v_mctx_1482_; lean_object* v_lctx_1483_; lean_object* v_options_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1479_ = lean_st_ref_get(v___y_1477_);
v_env_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_ref(v_env_1480_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_st_ref_get(v___y_1475_);
v_mctx_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_mctx_1482_);
lean_dec(v___x_1481_);
v_lctx_1483_ = lean_ctor_get(v___y_1474_, 2);
v_options_1484_ = lean_ctor_get(v___y_1476_, 2);
lean_inc_ref(v_options_1484_);
lean_inc_ref(v_lctx_1483_);
v___x_1485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1485_, 0, v_env_1480_);
lean_ctor_set(v___x_1485_, 1, v_mctx_1482_);
lean_ctor_set(v___x_1485_, 2, v_lctx_1483_);
lean_ctor_set(v___x_1485_, 3, v_options_1484_);
v___x_1486_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_msgData_1473_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5___boxed(lean_object* v_msgData_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msgData_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_ref_1501_; lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_ref_1501_ = lean_ctor_get(v___y_1498_, 5);
v___x_1502_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_inc(v_ref_1501_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_ref_1501_);
lean_ctor_set(v___x_1507_, 1, v_a_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 1);
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg___boxed(lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(lean_object* v___x_1525_, lean_object* v_snd_1526_, lean_object* v_as_1527_, size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_a_1537_; uint8_t v___x_1541_; 
v___x_1541_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref(v_snd_1526_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_b_1530_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; lean_object* v_a_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_box(0);
v_a_1544_ = lean_array_uget_borrowed(v_as_1527_, v_i_1529_);
v___x_1545_ = l_Lean_Expr_isFVar(v_a_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v___x_1525_, v___x_1547_);
v___x_1549_ = l_Nat_reprFast(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = l_Lean_MessageData_ofFormat(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1546_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_inc_ref(v_snd_1526_);
v___x_1555_ = l_Lean_indentExpr(v_snd_1526_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1556_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref_known(v___x_1557_, 1);
v_a_1537_ = v___x_1543_;
goto v___jp_1536_;
}
else
{
lean_dec_ref(v_snd_1526_);
return v___x_1557_;
}
}
else
{
v_a_1537_ = v___x_1543_;
goto v___jp_1536_;
}
}
v___jp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1529_, v___x_1538_);
v_i_1529_ = v___x_1539_;
v_b_1530_ = v_a_1537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(lean_object* v___x_1558_, lean_object* v_snd_1559_, lean_object* v_as_1560_, lean_object* v_sz_1561_, lean_object* v_i_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1561_);
lean_dec(v_sz_1561_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1562_);
lean_dec(v_i_1562_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v___x_1558_, v_snd_1559_, v_as_1560_, v_sz_boxed_1569_, v_i_boxed_1570_, v_b_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec_ref(v_as_1560_);
lean_dec(v___x_1558_);
return v_res_1571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(lean_object* v___x_1581_, lean_object* v___x_1582_, lean_object* v_as_1583_, size_t v_sz_1584_, size_t v_i_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_lt(v_i_1585_, v_sz_1584_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
lean_dec(v___x_1581_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_b_1586_);
return v___x_1599_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
v_a_1600_ = lean_array_uget_borrowed(v_as_1583_, v_i_1585_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v_a_1600_);
v___x_1601_ = lean_infer_type(v_a_1600_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; uint8_t v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
lean_inc(v___x_1581_);
v___x_1603_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_a_1602_, v___x_1581_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1);
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = lean_nat_add(v_b_1586_, v___x_1605_);
v___x_1607_ = l_Nat_reprFast(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
v___x_1609_ = l_Lean_MessageData_ofFormat(v___x_1608_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1604_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_nat_add(v___x_1582_, v___x_1605_);
v___x_1614_ = l_Nat_reprFast(v___x_1613_);
v___x_1615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
v___x_1616_ = l_Lean_MessageData_ofFormat(v___x_1615_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1612_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_indentExpr(v_a_1602_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1621_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec_ref_known(v___x_1622_, 1);
goto v___jp_1592_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_b_1586_);
lean_dec(v___x_1581_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_dec(v_a_1602_);
goto v___jp_1592_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_b_1586_);
lean_dec(v___x_1581_);
v_a_1631_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1601_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1601_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
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
v___jp_1592_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_b_1586_, v___x_1593_);
lean_dec(v_b_1586_);
v___x_1595_ = ((size_t)1ULL);
v___x_1596_ = lean_usize_add(v_i_1585_, v___x_1595_);
v_i_1585_ = v___x_1596_;
v_b_1586_ = v___x_1594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(lean_object* v___x_1639_, lean_object* v___x_1640_, lean_object* v_as_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v___x_1639_, v___x_1640_, v_as_1641_, v_sz_boxed_1650_, v_i_boxed_1651_, v_b_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_as_1641_);
lean_dec(v___x_1640_);
return v_res_1652_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1653_; lean_object* v_dummy_1654_; 
v___x_1653_ = lean_box(0);
v_dummy_1654_ = l_Lean_Expr_sort___override(v___x_1653_);
return v_dummy_1654_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1));
v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(lean_object* v_fst_1670_, lean_object* v_fst_1671_, lean_object* v___x_1672_, lean_object* v_ys_1673_, lean_object* v_xType_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1745_; lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8));
v___x_1804_ = lean_unsigned_to_nat(3u);
v___x_1805_ = l_Lean_Expr_isAppOfArity(v_xType_1674_, v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10));
v___x_1807_ = lean_unsigned_to_nat(2u);
v___x_1808_ = l_Lean_Expr_isAppOfArity(v_xType_1674_, v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1672_);
lean_dec(v_fst_1671_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = l_Lean_Expr_appFn_x21(v_xType_1674_);
v___x_1812_ = l_Lean_Expr_appArg_x21(v___x_1811_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = l_Lean_Expr_appArg_x21(v_xType_1674_);
v_fst_1769_ = v___x_1812_;
v_snd_1770_ = v___x_1813_;
goto v___jp_1768_;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = l_Lean_Expr_appFn_x21(v_xType_1674_);
v___x_1815_ = l_Lean_Expr_appArg_x21(v___x_1814_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = l_Lean_Expr_appArg_x21(v_xType_1674_);
v_fst_1769_ = v___x_1815_;
v_snd_1770_ = v___x_1816_;
goto v___jp_1768_;
}
v___jp_1680_:
{
lean_object* v_dummy_1687_; lean_object* v_nargs_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v_dummy_1687_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_1688_ = l_Lean_Expr_getAppNumArgs(v___y_1682_);
lean_inc(v_nargs_1688_);
v___x_1689_ = lean_mk_array(v_nargs_1688_, v_dummy_1687_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_nat_sub(v_nargs_1688_, v___x_1690_);
lean_dec(v_nargs_1688_);
lean_inc_ref(v___y_1682_);
v___x_1692_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1682_, v___x_1689_, v___x_1691_);
v___x_1693_ = lean_box(0);
v_sz_1694_ = lean_array_size(v___x_1692_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v_fst_1670_, v___y_1682_, v___x_1692_, v_sz_1694_, v___x_1695_, v___x_1693_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec_ref(v___x_1692_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v___x_1696_, 0);
lean_dec(v_unused_1705_);
v___x_1698_ = v___x_1696_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v___x_1696_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1681_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
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
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v___y_1681_);
v_a_1706_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1696_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
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
v___jp_1714_:
{
lean_object* v___x_1721_; uint8_t v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = l_Lean_Expr_mvarId_x21(v___y_1716_);
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1721_, v_fst_1671_);
lean_dec(v_fst_1671_);
lean_dec(v___x_1721_);
v___x_1723_ = lean_bool_not(v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_fst_1670_, v___x_1725_);
v___x_1727_ = l_Nat_reprFast(v___x_1726_);
v___x_1728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
v___x_1729_ = l_Lean_MessageData_ofFormat(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1724_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
lean_inc_ref(v___y_1715_);
v___x_1733_ = l_Lean_indentExpr(v___y_1715_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1734_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref_known(v___x_1735_, 1);
v___y_1681_ = v___y_1716_;
v___y_1682_ = v___y_1715_;
v___y_1683_ = v___y_1717_;
v___y_1684_ = v___y_1718_;
v___y_1685_ = v___y_1719_;
v___y_1686_ = v___y_1720_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v___y_1716_);
lean_dec_ref(v___y_1715_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
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
else
{
v___y_1681_ = v___y_1716_;
v___y_1682_ = v___y_1715_;
v___y_1683_ = v___y_1717_;
v___y_1684_ = v___y_1718_;
v___y_1685_ = v___y_1719_;
v___y_1686_ = v___y_1720_;
goto v___jp_1680_;
}
}
v___jp_1744_:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = l_Lean_Expr_getAppFn(v___y_1745_);
v___x_1747_ = l_Lean_Expr_isMVar(v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_fst_1670_, v___x_1749_);
v___x_1751_ = l_Nat_reprFast(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
v___x_1753_ = l_Lean_MessageData_ofFormat(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1748_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
lean_inc_ref(v___y_1745_);
v___x_1757_ = l_Lean_indentExpr(v___y_1745_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1758_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_dec_ref_known(v___x_1759_, 1);
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___x_1746_;
v___y_1717_ = v___y_1675_;
v___y_1718_ = v___y_1676_;
v___y_1719_ = v___y_1677_;
v___y_1720_ = v___y_1678_;
goto v___jp_1714_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v___x_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v_fst_1671_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___x_1746_;
v___y_1717_ = v___y_1675_;
v___y_1718_ = v___y_1676_;
v___y_1719_ = v___y_1677_;
v___y_1720_ = v___y_1678_;
goto v___jp_1714_;
}
}
v___jp_1768_:
{
size_t v_sz_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v_sz_1771_ = lean_array_size(v_ys_1673_);
v___x_1772_ = ((size_t)0ULL);
lean_inc(v_fst_1671_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v_fst_1671_, v_fst_1670_, v_ys_1673_, v_sz_1771_, v___x_1772_, v___x_1672_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1773_) == 0)
{
uint8_t v___x_1774_; 
lean_dec_ref_known(v___x_1773_, 1);
lean_inc(v_fst_1671_);
v___x_1774_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_fst_1769_, v_fst_1671_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_fst_1670_, v___x_1776_);
v___x_1778_ = l_Nat_reprFast(v___x_1777_);
v___x_1779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
v___x_1780_ = l_Lean_MessageData_ofFormat(v___x_1779_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1775_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_indentExpr(v_fst_1769_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1785_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_dec_ref_known(v___x_1786_, 1);
v___y_1745_ = v_snd_1770_;
goto v___jp_1744_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_snd_1770_);
lean_dec(v_fst_1671_);
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
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
lean_dec_ref(v_fst_1769_);
v___y_1745_ = v_snd_1770_;
goto v___jp_1744_;
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_snd_1770_);
lean_dec_ref(v_fst_1769_);
lean_dec(v_fst_1671_);
v_a_1795_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1773_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1773_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(lean_object* v_fst_1817_, lean_object* v_fst_1818_, lean_object* v___x_1819_, lean_object* v_ys_1820_, lean_object* v_xType_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(v_fst_1817_, v_fst_1818_, v___x_1819_, v_ys_1820_, v_xType_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_xType_1821_);
lean_dec_ref(v_ys_1820_);
lean_dec(v_fst_1817_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(lean_object* v_as_1828_, size_t v_sz_1829_, size_t v_i_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_lt(v_i_1830_, v_sz_1829_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_b_1831_);
return v___x_1838_;
}
else
{
lean_object* v_snd_1839_; lean_object* v_snd_1840_; lean_object* v_snd_1841_; lean_object* v_fst_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1938_; 
v_snd_1839_ = lean_ctor_get(v_b_1831_, 1);
lean_inc(v_snd_1839_);
v_snd_1840_ = lean_ctor_get(v_snd_1839_, 1);
lean_inc(v_snd_1840_);
v_snd_1841_ = lean_ctor_get(v_snd_1840_, 1);
lean_inc(v_snd_1841_);
v_fst_1842_ = lean_ctor_get(v_b_1831_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_b_1831_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_b_1831_, 1);
lean_dec(v_unused_1939_);
v___x_1844_ = v_b_1831_;
v_isShared_1845_ = v_isSharedCheck_1938_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_fst_1842_);
lean_dec(v_b_1831_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1938_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_fst_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1936_; 
v_fst_1846_ = lean_ctor_get(v_snd_1839_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_snd_1839_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_snd_1839_, 1);
lean_dec(v_unused_1937_);
v___x_1848_ = v_snd_1839_;
v_isShared_1849_ = v_isSharedCheck_1936_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_fst_1846_);
lean_dec(v_snd_1839_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1936_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_fst_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1934_; 
v_fst_1850_ = lean_ctor_get(v_snd_1840_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_snd_1840_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_snd_1840_, 1);
lean_dec(v_unused_1935_);
v___x_1852_ = v_snd_1840_;
v_isShared_1853_ = v_isSharedCheck_1934_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_fst_1850_);
lean_dec(v_snd_1840_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1934_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_array_1854_; lean_object* v_start_1855_; lean_object* v_stop_1856_; uint8_t v___x_1857_; 
v_array_1854_ = lean_ctor_get(v_snd_1841_, 0);
v_start_1855_ = lean_ctor_get(v_snd_1841_, 1);
v_stop_1856_ = lean_ctor_get(v_snd_1841_, 2);
v___x_1857_ = lean_nat_dec_lt(v_start_1855_, v_stop_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1859_; 
if (v_isShared_1853_ == 0)
{
v___x_1859_ = v___x_1852_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_fst_1850_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_snd_1841_);
v___x_1859_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1859_);
v___x_1861_ = v___x_1848_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1846_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1861_);
v___x_1863_ = v___x_1844_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_fst_1842_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
}
else
{
lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1930_; 
lean_inc(v_stop_1856_);
lean_inc(v_start_1855_);
lean_inc_ref(v_array_1854_);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_snd_1841_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; lean_object* v_unused_1932_; lean_object* v_unused_1933_; 
v_unused_1931_ = lean_ctor_get(v_snd_1841_, 2);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_snd_1841_, 1);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_snd_1841_, 0);
lean_dec(v_unused_1933_);
v___x_1869_ = v_snd_1841_;
v_isShared_1870_ = v_isSharedCheck_1930_;
goto v_resetjp_1868_;
}
else
{
lean_dec(v_snd_1841_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1930_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___f_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1871_ = lean_unsigned_to_nat(0u);
v_a_1872_ = lean_array_uget_borrowed(v_as_1828_, v_i_1830_);
lean_inc(v_fst_1842_);
lean_inc(v_fst_1846_);
v___f_1873_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1873_, 0, v_fst_1846_);
lean_closure_set(v___f_1873_, 1, v_fst_1842_);
lean_closure_set(v___f_1873_, 2, v___x_1871_);
v___x_1874_ = lean_array_fget(v_array_1854_, v_start_1855_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_add(v_start_1855_, v___x_1875_);
lean_dec(v_start_1855_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v___x_1876_);
v___x_1878_ = v___x_1869_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_array_1854_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_stop_1856_);
v___x_1878_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v_foundMVars_1880_; lean_object* v_hypothesesPos_1881_; uint8_t v___y_1896_; uint8_t v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = lean_unbox(v___x_1874_);
lean_dec(v___x_1874_);
v___x_1925_ = l_Lean_BinderInfo_isExplicit(v___x_1924_);
if (v___x_1925_ == 0)
{
v___y_1896_ = v___x_1925_;
goto v___jp_1895_;
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; uint8_t v___x_1928_; 
v___x_1926_ = l_Lean_Expr_mvarId_x21(v_a_1872_);
v___x_1927_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1926_, v_fst_1842_);
lean_dec(v___x_1926_);
v___x_1928_ = lean_bool_not(v___x_1927_);
v___y_1896_ = v___x_1928_;
goto v___jp_1895_;
}
v___jp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_nat_add(v_fst_1846_, v___x_1875_);
lean_dec(v_fst_1846_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1878_);
lean_ctor_set(v___x_1852_, 0, v_hypothesesPos_1881_);
v___x_1884_ = v___x_1852_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_hypothesesPos_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1878_);
v___x_1884_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1884_);
lean_ctor_set(v___x_1848_, 0, v___x_1882_);
v___x_1886_ = v___x_1848_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1886_);
lean_ctor_set(v___x_1844_, 0, v_foundMVars_1880_);
v___x_1888_ = v___x_1844_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_foundMVars_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
size_t v___x_1889_; size_t v___x_1890_; 
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1830_, v___x_1889_);
v_i_1830_ = v___x_1890_;
v_b_1831_ = v___x_1888_;
goto _start;
}
}
}
}
v___jp_1895_:
{
if (v___y_1896_ == 0)
{
lean_dec_ref(v___f_1873_);
v_foundMVars_1880_ = v_fst_1842_;
v_hypothesesPos_1881_ = v_fst_1850_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1897_; 
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v_a_1872_);
v___x_1897_ = lean_infer_type(v_a_1872_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = 0;
v___x_1900_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_a_1898_, v___f_1873_, v___x_1899_, v___x_1899_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
if (lean_obj_tag(v_a_1901_) == 0)
{
v_foundMVars_1880_ = v_fst_1842_;
v_hypothesesPos_1881_ = v_fst_1850_;
goto v___jp_1879_;
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_val_1902_ = lean_ctor_get(v_a_1901_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_a_1901_, 1);
v___x_1903_ = l_Lean_Expr_mvarId_x21(v_a_1872_);
v___x_1904_ = l_Lean_MVarIdSet_insert(v_fst_1842_, v___x_1903_);
v___x_1905_ = l_Lean_Expr_mvarId_x21(v_val_1902_);
lean_dec(v_val_1902_);
v___x_1906_ = l_Lean_MVarIdSet_insert(v___x_1904_, v___x_1905_);
lean_inc(v_fst_1846_);
v___x_1907_ = lean_array_push(v_fst_1850_, v_fst_1846_);
v_foundMVars_1880_ = v___x_1906_;
v_hypothesesPos_1881_ = v___x_1907_;
goto v___jp_1879_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___x_1878_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_del_object(v___x_1848_);
lean_dec(v_fst_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_fst_1842_);
v_a_1908_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1900_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1900_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v___x_1878_);
lean_dec_ref(v___f_1873_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_del_object(v___x_1848_);
lean_dec(v_fst_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_fst_1842_);
v_a_1916_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1897_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1897_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_as_1940_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_as_1940_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(lean_object* v_as_1952_, size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_b_1955_){
_start:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_b_1955_);
return v___x_1958_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; 
v_a_1959_ = lean_array_uget_borrowed(v_as_1952_, v_i_1954_);
lean_inc(v_a_1959_);
v___x_1960_ = l_Lean_MVarIdSet_insert(v_b_1955_, v_a_1959_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_add(v_i_1954_, v___x_1961_);
v_i_1954_ = v___x_1962_;
v_b_1955_ = v___x_1960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(lean_object* v_as_1964_, lean_object* v_sz_1965_, lean_object* v_i_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_){
_start:
{
size_t v_sz_boxed_1969_; size_t v_i_boxed_1970_; lean_object* v_res_1971_; 
v_sz_boxed_1969_ = lean_unbox_usize(v_sz_1965_);
lean_dec(v_sz_1965_);
v_i_boxed_1970_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_1964_, v_sz_boxed_1969_, v_i_boxed_1970_, v_b_1967_);
lean_dec_ref(v_as_1964_);
return v_res_1971_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_unsigned_to_nat(16u);
v___x_1974_ = lean_mk_array(v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
return v___x_1977_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2));
v___x_1981_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(lean_object* v_as_1983_, size_t v_sz_1984_, size_t v_i_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_lt(v_i_1985_, v_sz_1984_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_b_1986_);
return v___x_1993_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_result_1997_; size_t v_sz_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v_a_1994_ = lean_array_uget_borrowed(v_as_1983_, v_i_1985_);
v___x_1995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3);
lean_inc(v_a_1994_);
v___x_1996_ = l_Lean_Expr_collectMVars(v___x_1995_, v_a_1994_);
v_result_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_result_1997_);
lean_dec_ref(v___x_1996_);
v_sz_1998_ = lean_array_size(v_result_1997_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_result_1997_, v_sz_1998_, v___x_1999_, v_b_1986_);
lean_dec_ref(v_result_1997_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; size_t v___x_2002_; size_t v___x_2003_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1985_, v___x_2002_);
v_i_1985_ = v___x_2003_;
v_b_1986_ = v_a_2001_;
goto _start;
}
else
{
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___boxed(lean_object* v_as_2005_, lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_as_2005_, v_sz_boxed_2014_, v_i_boxed_2015_, v_b_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v_as_2005_);
return v_res_2016_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(lean_object* v_lhsArgs_2022_, lean_object* v_fst_2023_, lean_object* v_fst_2024_, lean_object* v_lhsFn_2025_, lean_object* v_declName_2026_, lean_object* v_prio_2027_, lean_object* v_snd_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
if (lean_obj_tag(v_x_2029_) == 5)
{
lean_object* v_fn_2037_; lean_object* v_arg_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_fn_2037_ = lean_ctor_get(v_x_2029_, 0);
lean_inc_ref(v_fn_2037_);
v_arg_2038_ = lean_ctor_get(v_x_2029_, 1);
lean_inc_ref(v_arg_2038_);
lean_dec_ref_known(v_x_2029_, 2);
v___x_2039_ = lean_array_set(v_x_2030_, v_x_2031_, v_arg_2038_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_sub(v_x_2031_, v___x_2040_);
lean_dec(v_x_2031_);
v_x_2029_ = v_fn_2037_;
v_x_2030_ = v___x_2039_;
v_x_2031_ = v___x_2041_;
goto _start;
}
else
{
lean_object* v___x_2043_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2105_; uint8_t v___x_2112_; 
lean_dec(v_x_2031_);
v___x_2043_ = lean_box(1);
v___x_2112_ = l_Lean_Expr_isConst(v_lhsFn_2025_);
if (v___x_2112_ == 0)
{
v___y_2105_ = v___x_2112_;
goto v___jp_2104_;
}
else
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Lean_Expr_isConst(v_x_2029_);
v___y_2105_ = v___x_2113_;
goto v___jp_2104_;
}
v___jp_2044_:
{
size_t v_sz_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v_sz_2049_ = lean_array_size(v_lhsArgs_2022_);
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_lhsArgs_2022_, v_sz_2049_, v___x_2050_, v___x_2043_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; size_t v_sz_2060_; lean_object* v___x_2061_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0));
v___x_2055_ = lean_array_get_size(v_fst_2023_);
v___x_2056_ = l_Array_toSubarray___redArg(v_fst_2023_, v___x_2053_, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2053_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2052_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v_sz_2060_ = lean_array_size(v_fst_2024_);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_fst_2024_, v_sz_2060_, v___x_2050_, v___x_2059_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2074_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_snd_2066_; lean_object* v_snd_2067_; lean_object* v_fst_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v_snd_2066_ = lean_ctor_get(v_a_2062_, 1);
lean_inc(v_snd_2066_);
lean_dec(v_a_2062_);
v_snd_2067_ = lean_ctor_get(v_snd_2066_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_snd_2066_);
v_fst_2068_ = lean_ctor_get(v_snd_2067_, 0);
lean_inc(v_fst_2068_);
lean_dec(v_snd_2067_);
v___x_2069_ = l_Lean_Expr_constName_x21(v_lhsFn_2025_);
v___x_2070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2070_, 0, v_declName_2026_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_ctor_set(v___x_2070_, 2, v_fst_2068_);
lean_ctor_set(v___x_2070_, 3, v_prio_2027_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2070_);
v___x_2072_ = v___x_2064_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_prio_2027_);
lean_dec(v_declName_2026_);
v_a_2075_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2061_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2061_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
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
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_prio_2027_);
lean_dec(v_declName_2026_);
lean_dec_ref(v_fst_2023_);
v_a_2083_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2051_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2051_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
v___jp_2091_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v___x_2092_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2);
v___x_2093_ = l_Lean_indentExpr(v_snd_2028_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_2094_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
v___jp_2104_:
{
if (v___y_2105_ == 0)
{
lean_dec_ref(v_x_2030_);
lean_dec_ref(v_x_2029_);
lean_dec(v_prio_2027_);
lean_dec(v_declName_2026_);
lean_dec_ref(v_fst_2023_);
goto v___jp_2091_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2106_ = l_Lean_Expr_constName_x21(v_lhsFn_2025_);
v___x_2107_ = l_Lean_Expr_constName_x21(v_x_2029_);
lean_dec_ref(v_x_2029_);
v___x_2108_ = lean_name_eq(v___x_2106_, v___x_2107_);
lean_dec(v___x_2107_);
lean_dec(v___x_2106_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v_x_2030_);
lean_dec(v_prio_2027_);
lean_dec(v_declName_2026_);
lean_dec_ref(v_fst_2023_);
goto v___jp_2091_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = lean_array_get_size(v_lhsArgs_2022_);
v___x_2110_ = lean_array_get_size(v_x_2030_);
lean_dec_ref(v_x_2030_);
v___x_2111_ = lean_nat_dec_eq(v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v_prio_2027_);
lean_dec(v_declName_2026_);
lean_dec_ref(v_fst_2023_);
goto v___jp_2091_;
}
else
{
lean_dec_ref(v_snd_2028_);
v___y_2045_ = v___y_2032_;
v___y_2046_ = v___y_2033_;
v___y_2047_ = v___y_2034_;
v___y_2048_ = v___y_2035_;
goto v___jp_2044_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___boxed(lean_object* v_lhsArgs_2114_, lean_object* v_fst_2115_, lean_object* v_fst_2116_, lean_object* v_lhsFn_2117_, lean_object* v_declName_2118_, lean_object* v_prio_2119_, lean_object* v_snd_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_lhsArgs_2114_, v_fst_2115_, v_fst_2116_, v_lhsFn_2117_, v_declName_2118_, v_prio_2119_, v_snd_2120_, v_x_2121_, v_x_2122_, v_x_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_lhsFn_2117_);
lean_dec_ref(v_fst_2116_);
lean_dec_ref(v_lhsArgs_2114_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(lean_object* v_snd_2130_, lean_object* v_fst_2131_, lean_object* v_fst_2132_, lean_object* v_declName_2133_, lean_object* v_prio_2134_, lean_object* v_snd_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 5)
{
lean_object* v_fn_2144_; lean_object* v_arg_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_fn_2144_ = lean_ctor_get(v_x_2136_, 0);
lean_inc_ref(v_fn_2144_);
v_arg_2145_ = lean_ctor_get(v_x_2136_, 1);
lean_inc_ref(v_arg_2145_);
lean_dec_ref_known(v_x_2136_, 2);
v___x_2146_ = lean_array_set(v_x_2137_, v_x_2138_, v_arg_2145_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_sub(v_x_2138_, v___x_2147_);
lean_dec(v_x_2138_);
v_x_2136_ = v_fn_2144_;
v_x_2137_ = v___x_2146_;
v_x_2138_ = v___x_2148_;
goto _start;
}
else
{
lean_object* v_dummy_2150_; lean_object* v_nargs_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v_x_2138_);
v_dummy_2150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2151_ = l_Lean_Expr_getAppNumArgs(v_snd_2130_);
lean_inc(v_nargs_2151_);
v___x_2152_ = lean_mk_array(v_nargs_2151_, v_dummy_2150_);
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v_nargs_2151_, v___x_2153_);
lean_dec(v_nargs_2151_);
v___x_2155_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_x_2137_, v_fst_2131_, v_fst_2132_, v_x_2136_, v_declName_2133_, v_prio_2134_, v_snd_2135_, v_snd_2130_, v___x_2152_, v___x_2154_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec_ref(v_x_2136_);
lean_dec_ref(v_x_2137_);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12___boxed(lean_object* v_snd_2156_, lean_object* v_fst_2157_, lean_object* v_fst_2158_, lean_object* v_declName_2159_, lean_object* v_prio_2160_, lean_object* v_snd_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_2156_, v_fst_2157_, v_fst_2158_, v_declName_2159_, v_prio_2160_, v_snd_2161_, v_x_2162_, v_x_2163_, v_x_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_fst_2158_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(lean_object* v_fst_2171_, lean_object* v_fst_2172_, lean_object* v_declName_2173_, lean_object* v_prio_2174_, lean_object* v_snd_2175_, lean_object* v_snd_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 5)
{
lean_object* v_fn_2185_; lean_object* v_arg_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_fn_2185_ = lean_ctor_get(v_x_2177_, 0);
lean_inc_ref(v_fn_2185_);
v_arg_2186_ = lean_ctor_get(v_x_2177_, 1);
lean_inc_ref(v_arg_2186_);
lean_dec_ref_known(v_x_2177_, 2);
v___x_2187_ = lean_array_set(v_x_2178_, v_x_2179_, v_arg_2186_);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_sub(v_x_2179_, v___x_2188_);
v___x_2190_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_2176_, v_fst_2171_, v_fst_2172_, v_declName_2173_, v_prio_2174_, v_snd_2175_, v_fn_2185_, v___x_2187_, v___x_2189_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2190_;
}
else
{
lean_object* v_dummy_2191_; lean_object* v_nargs_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_dummy_2191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2192_ = l_Lean_Expr_getAppNumArgs(v_snd_2176_);
lean_inc(v_nargs_2192_);
v___x_2193_ = lean_mk_array(v_nargs_2192_, v_dummy_2191_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v_nargs_2192_, v___x_2194_);
lean_dec(v_nargs_2192_);
v___x_2196_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_x_2178_, v_fst_2171_, v_fst_2172_, v_x_2177_, v_declName_2173_, v_prio_2174_, v_snd_2175_, v_snd_2176_, v___x_2193_, v___x_2195_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec_ref(v_x_2177_);
lean_dec_ref(v_x_2178_);
return v___x_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(lean_object* v_fst_2197_, lean_object* v_fst_2198_, lean_object* v_declName_2199_, lean_object* v_prio_2200_, lean_object* v_snd_2201_, lean_object* v_snd_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_, lean_object* v_x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(v_fst_2197_, v_fst_2198_, v_declName_2199_, v_prio_2200_, v_snd_2201_, v_snd_2202_, v_x_2203_, v_x_2204_, v_x_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_x_2205_);
lean_dec_ref(v_fst_2198_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
if (lean_obj_tag(v_a_2212_) == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = l_List_reverse___redArg(v_a_2213_);
return v___x_2214_;
}
else
{
lean_object* v_head_2215_; lean_object* v_tail_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2225_; 
v_head_2215_ = lean_ctor_get(v_a_2212_, 0);
v_tail_2216_ = lean_ctor_get(v_a_2212_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2212_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2218_ = v_a_2212_;
v_isShared_2219_ = v_isSharedCheck_2225_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_tail_2216_);
lean_inc(v_head_2215_);
lean_dec(v_a_2212_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2225_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_mkLevelParam(v_head_2215_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_a_2213_);
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2213_);
v___x_2222_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
v_a_2212_ = v_tail_2216_;
v_a_2213_ = v___x_2222_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
lean_ctor_set(v___x_2231_, 2, v___x_2230_);
lean_ctor_set(v___x_2231_, 3, v___x_2230_);
lean_ctor_set(v___x_2231_, 4, v___x_2229_);
lean_ctor_set(v___x_2231_, 5, v___x_2229_);
lean_ctor_set(v___x_2231_, 6, v___x_2229_);
lean_ctor_set(v___x_2231_, 7, v___x_2229_);
lean_ctor_set(v___x_2231_, 8, v___x_2229_);
lean_ctor_set(v___x_2231_, 9, v___x_2229_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_unsigned_to_nat(32u);
v___x_2233_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = ((size_t)5ULL);
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = lean_unsigned_to_nat(32u);
v___x_2238_ = lean_mk_empty_array_with_capacity(v___x_2237_);
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_2240_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set(v___x_2240_, 2, v___x_2236_);
lean_ctor_set(v___x_2240_, 3, v___x_2236_);
lean_ctor_set_usize(v___x_2240_, 4, v___x_2235_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = lean_box(1);
v___x_2242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_2243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_2244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
lean_ctor_set(v___x_2244_, 2, v___x_2241_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v_env_2271_; uint8_t v___y_2273_; uint8_t v___x_2329_; uint8_t v___x_2330_; 
v___x_2270_ = lean_st_ref_get(v___y_2268_);
v_env_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc_ref(v_env_2271_);
lean_dec(v___x_2270_);
v___x_2329_ = l_Lean_Name_isAnonymous(v_declHint_2267_);
v___x_2330_ = lean_bool_not(v___x_2329_);
if (v___x_2330_ == 0)
{
v___y_2273_ = v___x_2330_;
goto v___jp_2272_;
}
else
{
uint8_t v_isExporting_2331_; 
v_isExporting_2331_ = lean_ctor_get_uint8(v_env_2271_, sizeof(void*)*8);
v___y_2273_ = v_isExporting_2331_;
goto v___jp_2272_;
}
v___jp_2272_:
{
if (v___y_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_dec_ref(v_env_2271_);
lean_dec(v_declHint_2267_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_msg_2266_);
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = 0;
lean_inc_ref(v_env_2271_);
v___x_2276_ = l_Lean_Environment_setExporting(v_env_2271_, v___x_2275_);
lean_inc(v_declHint_2267_);
lean_inc_ref(v___x_2276_);
v___x_2277_ = l_Lean_Environment_contains(v___x_2276_, v_declHint_2267_, v___y_2273_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
lean_dec_ref(v___x_2276_);
lean_dec_ref(v_env_2271_);
lean_dec(v_declHint_2267_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_msg_2266_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_c_2284_; lean_object* v___x_2285_; 
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_2280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_2281_ = l_Lean_Options_empty;
v___x_2282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2276_);
lean_ctor_set(v___x_2282_, 1, v___x_2279_);
lean_ctor_set(v___x_2282_, 2, v___x_2280_);
lean_ctor_set(v___x_2282_, 3, v___x_2281_);
lean_inc(v_declHint_2267_);
v___x_2283_ = l_Lean_MessageData_ofConstName(v_declHint_2267_, v___x_2275_);
v_c_2284_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2284_, 0, v___x_2282_);
lean_ctor_set(v_c_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2271_, v_declHint_2267_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v_env_2271_);
lean_dec(v_declHint_2267_);
v___x_2286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_c_2284_);
v___x_2288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_note(v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_msg_2266_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
else
{
lean_object* v_val_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2328_; 
v_val_2293_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2295_ = v___x_2285_;
v_isShared_2296_ = v_isSharedCheck_2328_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_val_2293_);
lean_dec(v___x_2285_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2328_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_mod_2300_; uint8_t v___x_2301_; 
v___x_2297_ = lean_box(0);
v___x_2298_ = l_Lean_Environment_header(v_env_2271_);
lean_dec_ref(v_env_2271_);
v___x_2299_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2298_);
v_mod_2300_ = lean_array_get(v___x_2297_, v___x_2299_, v_val_2293_);
lean_dec(v_val_2293_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = l_Lean_isPrivateName(v_declHint_2267_);
lean_dec(v_declHint_2267_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_c_2284_);
v___x_2304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_MessageData_ofName(v_mod_2300_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_MessageData_note(v___x_2309_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_msg_2266_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set_tag(v___x_2295_, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2311_);
v___x_2313_ = v___x_2295_;
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
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v_c_2284_);
v___x_2317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofName(v_mod_2300_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_MessageData_note(v___x_2322_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_msg_2266_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set_tag(v___x_2295_, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2324_);
v___x_2326_ = v___x_2295_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_2332_, lean_object* v_declHint_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2332_, v_declHint_2333_, v___y_2334_);
lean_dec(v___y_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(lean_object* v_msg_2337_, lean_object* v_declHint_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2354_; 
v___x_2344_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2337_, v_declHint_2338_, v___y_2342_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2354_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2354_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2349_ = l_Lean_unknownIdentifierMessageTag;
v___x_2350_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_a_2345_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2350_);
v___x_2352_ = v___x_2347_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16___boxed(lean_object* v_msg_2355_, lean_object* v_declHint_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_2355_, v_declHint_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(lean_object* v_ref_2363_, lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_fileName_2370_; lean_object* v_fileMap_2371_; lean_object* v_options_2372_; lean_object* v_currRecDepth_2373_; lean_object* v_maxRecDepth_2374_; lean_object* v_ref_2375_; lean_object* v_currNamespace_2376_; lean_object* v_openDecls_2377_; lean_object* v_initHeartbeats_2378_; lean_object* v_maxHeartbeats_2379_; lean_object* v_quotContext_2380_; lean_object* v_currMacroScope_2381_; uint8_t v_diag_2382_; lean_object* v_cancelTk_x3f_2383_; uint8_t v_suppressElabErrors_2384_; lean_object* v_inheritedTraceOptions_2385_; lean_object* v_ref_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_fileName_2370_ = lean_ctor_get(v___y_2367_, 0);
v_fileMap_2371_ = lean_ctor_get(v___y_2367_, 1);
v_options_2372_ = lean_ctor_get(v___y_2367_, 2);
v_currRecDepth_2373_ = lean_ctor_get(v___y_2367_, 3);
v_maxRecDepth_2374_ = lean_ctor_get(v___y_2367_, 4);
v_ref_2375_ = lean_ctor_get(v___y_2367_, 5);
v_currNamespace_2376_ = lean_ctor_get(v___y_2367_, 6);
v_openDecls_2377_ = lean_ctor_get(v___y_2367_, 7);
v_initHeartbeats_2378_ = lean_ctor_get(v___y_2367_, 8);
v_maxHeartbeats_2379_ = lean_ctor_get(v___y_2367_, 9);
v_quotContext_2380_ = lean_ctor_get(v___y_2367_, 10);
v_currMacroScope_2381_ = lean_ctor_get(v___y_2367_, 11);
v_diag_2382_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*14);
v_cancelTk_x3f_2383_ = lean_ctor_get(v___y_2367_, 12);
v_suppressElabErrors_2384_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2385_ = lean_ctor_get(v___y_2367_, 13);
v_ref_2386_ = l_Lean_replaceRef(v_ref_2363_, v_ref_2375_);
lean_inc_ref(v_inheritedTraceOptions_2385_);
lean_inc(v_cancelTk_x3f_2383_);
lean_inc(v_currMacroScope_2381_);
lean_inc(v_quotContext_2380_);
lean_inc(v_maxHeartbeats_2379_);
lean_inc(v_initHeartbeats_2378_);
lean_inc(v_openDecls_2377_);
lean_inc(v_currNamespace_2376_);
lean_inc(v_maxRecDepth_2374_);
lean_inc(v_currRecDepth_2373_);
lean_inc_ref(v_options_2372_);
lean_inc_ref(v_fileMap_2371_);
lean_inc_ref(v_fileName_2370_);
v___x_2387_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2387_, 0, v_fileName_2370_);
lean_ctor_set(v___x_2387_, 1, v_fileMap_2371_);
lean_ctor_set(v___x_2387_, 2, v_options_2372_);
lean_ctor_set(v___x_2387_, 3, v_currRecDepth_2373_);
lean_ctor_set(v___x_2387_, 4, v_maxRecDepth_2374_);
lean_ctor_set(v___x_2387_, 5, v_ref_2386_);
lean_ctor_set(v___x_2387_, 6, v_currNamespace_2376_);
lean_ctor_set(v___x_2387_, 7, v_openDecls_2377_);
lean_ctor_set(v___x_2387_, 8, v_initHeartbeats_2378_);
lean_ctor_set(v___x_2387_, 9, v_maxHeartbeats_2379_);
lean_ctor_set(v___x_2387_, 10, v_quotContext_2380_);
lean_ctor_set(v___x_2387_, 11, v_currMacroScope_2381_);
lean_ctor_set(v___x_2387_, 12, v_cancelTk_x3f_2383_);
lean_ctor_set(v___x_2387_, 13, v_inheritedTraceOptions_2385_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*14, v_diag_2382_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*14 + 1, v_suppressElabErrors_2384_);
v___x_2388_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_2364_, v___y_2365_, v___y_2366_, v___x_2387_, v___y_2368_);
lean_dec_ref_known(v___x_2387_, 14);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2389_, v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_ref_2389_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(lean_object* v_ref_2397_, lean_object* v_msg_2398_, lean_object* v_declHint_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_a_2406_; lean_object* v___x_2407_; 
v___x_2405_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_2398_, v_declHint_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2397_, v_a_2406_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg___boxed(lean_object* v_ref_2408_, lean_object* v_msg_2409_, lean_object* v_declHint_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2408_, v_msg_2409_, v_declHint_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v_ref_2408_);
return v_res_2416_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(lean_object* v_ref_2423_, lean_object* v_constName_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2430_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1);
v___x_2431_ = 0;
lean_inc(v_constName_2424_);
v___x_2432_ = l_Lean_MessageData_ofConstName(v_constName_2424_, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2423_, v___x_2435_, v_constName_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_ref_2437_, lean_object* v_constName_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2437_, v_constName_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v_ref_2437_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_ref_2451_; lean_object* v___x_2452_; 
v_ref_2451_ = lean_ctor_get(v___y_2448_, 5);
v___x_2452_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2451_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_constName_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object* v_constName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v_env_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = lean_st_ref_get(v___y_2464_);
v_env_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_env_2467_);
lean_dec(v___x_2466_);
v___x_2468_ = 0;
lean_inc(v_constName_2460_);
v___x_2469_ = l_Lean_Environment_findConstVal_x3f(v_env_2467_, v_constName_2460_, v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2470_;
}
else
{
lean_object* v_val_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_constName_2460_);
v_val_2471_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2469_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_val_2471_);
lean_dec(v___x_2469_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 0);
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_val_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(lean_object* v_constName_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object* v_constName_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
lean_inc(v_constName_2486_);
v___x_2492_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2504_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_levelParams_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v_levelParams_2497_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_levelParams_2497_);
lean_dec(v_a_2493_);
v___x_2498_ = lean_box(0);
v___x_2499_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(v_levelParams_2497_, v___x_2498_);
v___x_2500_ = l_Lean_mkConst(v_constName_2486_, v___x_2499_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2500_);
v___x_2502_ = v___x_2495_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_constName_2486_);
v_a_2505_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2492_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2492_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(lean_object* v_constName_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(v_constName_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
static uint64_t _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0(void){
_start:
{
uint8_t v___x_2520_; uint64_t v___x_2521_; 
v___x_2520_ = 2;
v___x_2521_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Meta_mkSimpCongrTheorem___closed__1));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem(lean_object* v_declName_2525_, lean_object* v_prio_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2532_; uint8_t v_foApprox_2533_; uint8_t v_ctxApprox_2534_; uint8_t v_quasiPatternApprox_2535_; uint8_t v_constApprox_2536_; uint8_t v_isDefEqStuckEx_2537_; uint8_t v_unificationHints_2538_; uint8_t v_proofIrrelevance_2539_; uint8_t v_assignSyntheticOpaque_2540_; uint8_t v_offsetCnstrs_2541_; uint8_t v_etaStruct_2542_; uint8_t v_univApprox_2543_; uint8_t v_iota_2544_; uint8_t v_beta_2545_; uint8_t v_proj_2546_; uint8_t v_zeta_2547_; uint8_t v_zetaDelta_2548_; uint8_t v_zetaUnused_2549_; uint8_t v_zetaHave_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2643_; 
v___x_2532_ = l_Lean_Meta_Context_config(v_a_2527_);
v_foApprox_2533_ = lean_ctor_get_uint8(v___x_2532_, 0);
v_ctxApprox_2534_ = lean_ctor_get_uint8(v___x_2532_, 1);
v_quasiPatternApprox_2535_ = lean_ctor_get_uint8(v___x_2532_, 2);
v_constApprox_2536_ = lean_ctor_get_uint8(v___x_2532_, 3);
v_isDefEqStuckEx_2537_ = lean_ctor_get_uint8(v___x_2532_, 4);
v_unificationHints_2538_ = lean_ctor_get_uint8(v___x_2532_, 5);
v_proofIrrelevance_2539_ = lean_ctor_get_uint8(v___x_2532_, 6);
v_assignSyntheticOpaque_2540_ = lean_ctor_get_uint8(v___x_2532_, 7);
v_offsetCnstrs_2541_ = lean_ctor_get_uint8(v___x_2532_, 8);
v_etaStruct_2542_ = lean_ctor_get_uint8(v___x_2532_, 10);
v_univApprox_2543_ = lean_ctor_get_uint8(v___x_2532_, 11);
v_iota_2544_ = lean_ctor_get_uint8(v___x_2532_, 12);
v_beta_2545_ = lean_ctor_get_uint8(v___x_2532_, 13);
v_proj_2546_ = lean_ctor_get_uint8(v___x_2532_, 14);
v_zeta_2547_ = lean_ctor_get_uint8(v___x_2532_, 15);
v_zetaDelta_2548_ = lean_ctor_get_uint8(v___x_2532_, 16);
v_zetaUnused_2549_ = lean_ctor_get_uint8(v___x_2532_, 17);
v_zetaHave_2550_ = lean_ctor_get_uint8(v___x_2532_, 18);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2552_ = v___x_2532_;
v_isShared_2553_ = v_isSharedCheck_2643_;
goto v_resetjp_2551_;
}
else
{
lean_dec(v___x_2532_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2643_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v_trackZetaDelta_2554_; lean_object* v_zetaDeltaSet_2555_; lean_object* v_lctx_2556_; lean_object* v_localInstances_2557_; lean_object* v_defEqCtx_x3f_2558_; lean_object* v_synthPendingDepth_2559_; lean_object* v_canUnfold_x3f_2560_; uint8_t v_univApprox_2561_; uint8_t v_inTypeClassResolution_2562_; uint8_t v_cacheInferType_2563_; uint8_t v___x_2564_; lean_object* v_config_2566_; 
v_trackZetaDelta_2554_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7);
v_zetaDeltaSet_2555_ = lean_ctor_get(v_a_2527_, 1);
v_lctx_2556_ = lean_ctor_get(v_a_2527_, 2);
v_localInstances_2557_ = lean_ctor_get(v_a_2527_, 3);
v_defEqCtx_x3f_2558_ = lean_ctor_get(v_a_2527_, 4);
v_synthPendingDepth_2559_ = lean_ctor_get(v_a_2527_, 5);
v_canUnfold_x3f_2560_ = lean_ctor_get(v_a_2527_, 6);
v_univApprox_2561_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2562_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 2);
v_cacheInferType_2563_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 3);
v___x_2564_ = 2;
if (v_isShared_2553_ == 0)
{
v_config_2566_ = v___x_2552_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 0, v_foApprox_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 1, v_ctxApprox_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 2, v_quasiPatternApprox_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 3, v_constApprox_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 4, v_isDefEqStuckEx_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 5, v_unificationHints_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 6, v_proofIrrelevance_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 7, v_assignSyntheticOpaque_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 8, v_offsetCnstrs_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 10, v_etaStruct_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 11, v_univApprox_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 12, v_iota_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 13, v_beta_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 14, v_proj_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 15, v_zeta_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 16, v_zetaDelta_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 17, v_zetaUnused_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, 18, v_zetaHave_2550_);
v_config_2566_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
uint64_t v___x_2567_; uint64_t v___x_2568_; uint64_t v___x_2569_; uint64_t v___x_2570_; uint64_t v___x_2571_; uint64_t v_key_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_ctor_set_uint8(v_config_2566_, 9, v___x_2564_);
v___x_2567_ = l_Lean_Meta_Context_configKey(v_a_2527_);
v___x_2568_ = 3ULL;
v___x_2569_ = lean_uint64_shift_right(v___x_2567_, v___x_2568_);
v___x_2570_ = lean_uint64_shift_left(v___x_2569_, v___x_2568_);
v___x_2571_ = lean_uint64_once(&l_Lean_Meta_mkSimpCongrTheorem___closed__0, &l_Lean_Meta_mkSimpCongrTheorem___closed__0_once, _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0);
v_key_2572_ = lean_uint64_lor(v___x_2570_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2573_, 0, v_config_2566_);
lean_ctor_set_uint64(v___x_2573_, sizeof(void*)*1, v_key_2572_);
lean_inc(v_canUnfold_x3f_2560_);
lean_inc(v_synthPendingDepth_2559_);
lean_inc(v_defEqCtx_x3f_2558_);
lean_inc_ref(v_localInstances_2557_);
lean_inc_ref(v_lctx_2556_);
lean_inc(v_zetaDeltaSet_2555_);
v___x_2574_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v_zetaDeltaSet_2555_);
lean_ctor_set(v___x_2574_, 2, v_lctx_2556_);
lean_ctor_set(v___x_2574_, 3, v_localInstances_2557_);
lean_ctor_set(v___x_2574_, 4, v_defEqCtx_x3f_2558_);
lean_ctor_set(v___x_2574_, 5, v_synthPendingDepth_2559_);
lean_ctor_set(v___x_2574_, 6, v_canUnfold_x3f_2560_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*7, v_trackZetaDelta_2554_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*7 + 1, v_univApprox_2561_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2562_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*7 + 3, v_cacheInferType_2563_);
lean_inc(v_declName_2525_);
v___x_2575_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(v_declName_2525_, v___x_2574_, v_a_2528_, v_a_2529_, v_a_2530_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
lean_inc(v_a_2530_);
lean_inc_ref(v_a_2529_);
lean_inc(v_a_2528_);
lean_inc_ref(v___x_2574_);
v___x_2577_ = lean_infer_type(v_a_2576_, v___x_2574_, v_a_2528_, v_a_2529_, v_a_2530_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = lean_box(0);
v___x_2580_ = 0;
v___x_2581_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2578_, v___x_2579_, v___x_2580_, v___x_2574_, v_a_2528_, v_a_2529_, v_a_2530_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_snd_2583_; lean_object* v_fst_2584_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2617_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_snd_2583_ = lean_ctor_get(v_a_2582_, 1);
lean_inc(v_snd_2583_);
v_fst_2584_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_fst_2584_);
lean_dec(v_a_2582_);
v_fst_2585_ = lean_ctor_get(v_snd_2583_, 0);
v_snd_2586_ = lean_ctor_get(v_snd_2583_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_snd_2583_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2588_ = v_snd_2583_;
v_isShared_2589_ = v_isSharedCheck_2617_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_inc(v_fst_2585_);
lean_dec(v_snd_2583_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2617_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_fst_2591_; lean_object* v_snd_2592_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8));
v___x_2600_ = lean_unsigned_to_nat(3u);
v___x_2601_ = l_Lean_Expr_isAppOfArity(v_snd_2586_, v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10));
v___x_2603_ = lean_unsigned_to_nat(2u);
v___x_2604_ = l_Lean_Expr_isAppOfArity(v_snd_2586_, v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v_fst_2585_);
lean_dec(v_fst_2584_);
lean_dec(v_prio_2526_);
lean_dec(v_declName_2525_);
v___x_2605_ = lean_obj_once(&l_Lean_Meta_mkSimpCongrTheorem___closed__2, &l_Lean_Meta_mkSimpCongrTheorem___closed__2_once, _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2);
v___x_2606_ = l_Lean_indentExpr(v_snd_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 7);
lean_ctor_set(v___x_2588_, 1, v___x_2606_);
lean_ctor_set(v___x_2588_, 0, v___x_2605_);
v___x_2608_ = v___x_2588_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_2608_, v___x_2574_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec_ref_known(v___x_2574_, 7);
return v___x_2609_;
}
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_del_object(v___x_2588_);
v___x_2611_ = l_Lean_Expr_appFn_x21(v_snd_2586_);
v___x_2612_ = l_Lean_Expr_appArg_x21(v___x_2611_);
lean_dec_ref(v___x_2611_);
v___x_2613_ = l_Lean_Expr_appArg_x21(v_snd_2586_);
v_fst_2591_ = v___x_2612_;
v_snd_2592_ = v___x_2613_;
goto v___jp_2590_;
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_del_object(v___x_2588_);
v___x_2614_ = l_Lean_Expr_appFn_x21(v_snd_2586_);
v___x_2615_ = l_Lean_Expr_appArg_x21(v___x_2614_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = l_Lean_Expr_appArg_x21(v_snd_2586_);
v_fst_2591_ = v___x_2615_;
v_snd_2592_ = v___x_2616_;
goto v___jp_2590_;
}
v___jp_2590_:
{
lean_object* v_dummy_2593_; lean_object* v_nargs_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_dummy_2593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2594_ = l_Lean_Expr_getAppNumArgs(v_fst_2591_);
lean_inc(v_nargs_2594_);
v___x_2595_ = lean_mk_array(v_nargs_2594_, v_dummy_2593_);
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_sub(v_nargs_2594_, v___x_2596_);
lean_dec(v_nargs_2594_);
v___x_2598_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(v_fst_2585_, v_fst_2584_, v_declName_2525_, v_prio_2526_, v_snd_2586_, v_snd_2592_, v_fst_2591_, v___x_2595_, v___x_2597_, v___x_2574_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec_ref_known(v___x_2574_, 7);
lean_dec(v___x_2597_);
lean_dec(v_fst_2584_);
return v___x_2598_;
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref_known(v___x_2574_, 7);
lean_dec(v_prio_2526_);
lean_dec(v_declName_2525_);
v_a_2618_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2581_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2581_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref_known(v___x_2574_, 7);
lean_dec(v_prio_2526_);
lean_dec(v_declName_2525_);
v_a_2626_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2577_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2577_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref_known(v___x_2574_, 7);
lean_dec(v_prio_2526_);
lean_dec(v_declName_2525_);
v_a_2634_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2575_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2575_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem___boxed(lean_object* v_declName_2644_, lean_object* v_prio_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_Meta_mkSimpCongrTheorem(v_declName_2644_, v_prio_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(lean_object* v_as_2652_, size_t v_sz_2653_, size_t v_i_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_2652_, v_sz_2653_, v_i_2654_, v_b_2655_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(lean_object* v_as_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
size_t v_sz_boxed_2671_; size_t v_i_boxed_2672_; lean_object* v_res_2673_; 
v_sz_boxed_2671_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(v_as_2662_, v_sz_boxed_2671_, v_i_boxed_2672_, v_b_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec_ref(v_as_2662_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(lean_object* v_00_u03b1_2674_, lean_object* v_msg_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___boxed(lean_object* v_00_u03b1_2682_, lean_object* v_msg_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(v_00_u03b1_2682_, v_msg_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(lean_object* v_00_u03b1_2690_, lean_object* v_constName_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2698_, lean_object* v_constName_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(v_00_u03b1_2698_, v_constName_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(lean_object* v_00_u03b1_2706_, lean_object* v_ref_2707_, lean_object* v_constName_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2707_, v_constName_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_ref_2716_, lean_object* v_constName_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(v_00_u03b1_2715_, v_ref_2716_, v_constName_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_ref_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(lean_object* v_00_u03b1_2724_, lean_object* v_ref_2725_, lean_object* v_msg_2726_, lean_object* v_declHint_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2725_, v_msg_2726_, v_declHint_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_ref_2735_, lean_object* v_msg_2736_, lean_object* v_declHint_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(v_00_u03b1_2734_, v_ref_2735_, v_msg_2736_, v_declHint_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v_ref_2735_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(lean_object* v_msg_2744_, lean_object* v_declHint_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2744_, v_declHint_2745_, v___y_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2752_, lean_object* v_declHint_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(v_msg_2752_, v_declHint_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(lean_object* v_00_u03b1_2760_, lean_object* v_ref_2761_, lean_object* v_msg_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2761_, v_msg_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_ref_2770_, lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(v_00_u03b1_2769_, v_ref_2770_, v_msg_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v_ref_2770_);
return v_res_2777_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2778_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
return v___x_2782_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
v___x_2784_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
lean_ctor_set(v___x_2784_, 3, v___x_2783_);
lean_ctor_set(v___x_2784_, 4, v___x_2783_);
lean_ctor_set(v___x_2784_, 5, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(lean_object* v_ext_2785_, lean_object* v_b_2786_, uint8_t v_kind_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_currNamespace_2792_; lean_object* v___x_2793_; lean_object* v_env_2794_; lean_object* v_nextMacroScope_2795_; lean_object* v_ngen_2796_; lean_object* v_auxDeclNGen_2797_; lean_object* v_traceState_2798_; lean_object* v_messages_2799_; lean_object* v_infoState_2800_; lean_object* v_snapshotTasks_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2828_; 
v_currNamespace_2792_ = lean_ctor_get(v___y_2789_, 6);
v___x_2793_ = lean_st_ref_take(v___y_2790_);
v_env_2794_ = lean_ctor_get(v___x_2793_, 0);
v_nextMacroScope_2795_ = lean_ctor_get(v___x_2793_, 1);
v_ngen_2796_ = lean_ctor_get(v___x_2793_, 2);
v_auxDeclNGen_2797_ = lean_ctor_get(v___x_2793_, 3);
v_traceState_2798_ = lean_ctor_get(v___x_2793_, 4);
v_messages_2799_ = lean_ctor_get(v___x_2793_, 6);
v_infoState_2800_ = lean_ctor_get(v___x_2793_, 7);
v_snapshotTasks_2801_ = lean_ctor_get(v___x_2793_, 8);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v___x_2793_, 5);
lean_dec(v_unused_2829_);
v___x_2803_ = v___x_2793_;
v_isShared_2804_ = v_isSharedCheck_2828_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_snapshotTasks_2801_);
lean_inc(v_infoState_2800_);
lean_inc(v_messages_2799_);
lean_inc(v_traceState_2798_);
lean_inc(v_auxDeclNGen_2797_);
lean_inc(v_ngen_2796_);
lean_inc(v_nextMacroScope_2795_);
lean_inc(v_env_2794_);
lean_dec(v___x_2793_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2828_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_inc(v_currNamespace_2792_);
v___x_2805_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2794_, v_ext_2785_, v_b_2786_, v_kind_2787_, v_currNamespace_2792_);
v___x_2806_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 5, v___x_2806_);
lean_ctor_set(v___x_2803_, 0, v___x_2805_);
v___x_2808_ = v___x_2803_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_nextMacroScope_2795_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_ngen_2796_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_auxDeclNGen_2797_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_traceState_2798_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2827_, 6, v_messages_2799_);
lean_ctor_set(v_reuseFailAlloc_2827_, 7, v_infoState_2800_);
lean_ctor_set(v_reuseFailAlloc_2827_, 8, v_snapshotTasks_2801_);
v___x_2808_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_mctx_2811_; lean_object* v_zetaDeltaFVarIds_2812_; lean_object* v_postponed_2813_; lean_object* v_diag_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2825_; 
v___x_2809_ = lean_st_ref_set(v___y_2790_, v___x_2808_);
v___x_2810_ = lean_st_ref_take(v___y_2788_);
v_mctx_2811_ = lean_ctor_get(v___x_2810_, 0);
v_zetaDeltaFVarIds_2812_ = lean_ctor_get(v___x_2810_, 2);
v_postponed_2813_ = lean_ctor_get(v___x_2810_, 3);
v_diag_2814_ = lean_ctor_get(v___x_2810_, 4);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2810_, 1);
lean_dec(v_unused_2826_);
v___x_2816_ = v___x_2810_;
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_diag_2814_);
lean_inc(v_postponed_2813_);
lean_inc(v_zetaDeltaFVarIds_2812_);
lean_inc(v_mctx_2811_);
lean_dec(v___x_2810_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v___x_2818_);
v___x_2820_ = v___x_2816_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_mctx_2811_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_zetaDeltaFVarIds_2812_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_postponed_2813_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_diag_2814_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = lean_st_ref_set(v___y_2788_, v___x_2820_);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(lean_object* v_ext_2830_, lean_object* v_b_2831_, lean_object* v_kind_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v_kind_boxed_2837_; lean_object* v_res_2838_; 
v_kind_boxed_2837_ = lean_unbox(v_kind_2832_);
v_res_2838_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v_ext_2830_, v_b_2831_, v_kind_boxed_2837_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(lean_object* v_00_u03b1_2839_, lean_object* v_00_u03b2_2840_, lean_object* v_00_u03c3_2841_, lean_object* v_ext_2842_, lean_object* v_b_2843_, uint8_t v_kind_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v_ext_2842_, v_b_2843_, v_kind_2844_, v___y_2846_, v___y_2847_, v___y_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_00_u03b2_2852_, lean_object* v_00_u03c3_2853_, lean_object* v_ext_2854_, lean_object* v_b_2855_, lean_object* v_kind_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v_kind_boxed_2862_; lean_object* v_res_2863_; 
v_kind_boxed_2862_ = lean_unbox(v_kind_2856_);
v_res_2863_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(v_00_u03b1_2851_, v_00_u03b2_2852_, v_00_u03c3_2853_, v_ext_2854_, v_b_2855_, v_kind_boxed_2862_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem(lean_object* v_declName_2864_, uint8_t v_attrKind_2865_, lean_object* v_prio_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Meta_mkSimpCongrTheorem(v_declName_2864_, v_prio_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = l_Lean_Meta_congrExtension;
v___x_2875_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v___x_2874_, v_a_2873_, v_attrKind_2865_, v_a_2868_, v_a_2869_, v_a_2870_);
return v___x_2875_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2872_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2872_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem___boxed(lean_object* v_declName_2884_, lean_object* v_attrKind_2885_, lean_object* v_prio_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
uint8_t v_attrKind_boxed_2892_; lean_object* v_res_2893_; 
v_attrKind_boxed_2892_ = lean_unbox(v_attrKind_2885_);
v_res_2893_ = l_Lean_Meta_addSimpCongrTheorem(v_declName_2884_, v_attrKind_boxed_2892_, v_prio_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2893_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2900_; uint64_t v___x_2901_; 
v___x_2900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_2901_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2900_);
return v___x_2901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2902_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_2904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set_uint64(v___x_2904_, sizeof(void*)*1, v___x_2902_);
return v___x_2904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2909_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
lean_ctor_set(v___x_2909_, 2, v___x_2908_);
lean_ctor_set(v___x_2909_, 3, v___x_2908_);
lean_ctor_set(v___x_2909_, 4, v___x_2908_);
lean_ctor_set(v___x_2909_, 5, v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
lean_ctor_set(v___x_2911_, 2, v___x_2910_);
lean_ctor_set(v___x_2911_, 3, v___x_2910_);
lean_ctor_set(v___x_2911_, 4, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object* v___x_2912_, lean_object* v___x_2913_, lean_object* v_declName_2914_, lean_object* v_stx_2915_, uint8_t v_attrKind_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = l_Lean_Syntax_getArg(v_stx_2915_, v___x_2920_);
v___x_2922_ = l_Lean_getAttrParamOptPrio(v___x_2921_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; uint8_t v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = 0;
v___x_2925_ = 1;
v___x_2926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2928_ = lean_unsigned_to_nat(32u);
v___x_2929_ = lean_mk_empty_array_with_capacity(v___x_2928_);
v___x_2930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_2931_ = ((size_t)5ULL);
lean_inc_n(v___x_2912_, 6);
v___x_2932_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2929_);
lean_ctor_set(v___x_2932_, 2, v___x_2912_);
lean_ctor_set(v___x_2932_, 3, v___x_2912_);
lean_ctor_set_usize(v___x_2932_, 4, v___x_2931_);
v___x_2933_ = lean_box(1);
lean_inc_ref(v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2927_);
lean_ctor_set(v___x_2934_, 1, v___x_2932_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2912_);
v___x_2936_ = lean_box(0);
lean_inc(v___x_2913_);
v___x_2937_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2937_, 0, v___x_2926_);
lean_ctor_set(v___x_2937_, 1, v___x_2913_);
lean_ctor_set(v___x_2937_, 2, v___x_2934_);
lean_ctor_set(v___x_2937_, 3, v___x_2935_);
lean_ctor_set(v___x_2937_, 4, v___x_2936_);
lean_ctor_set(v___x_2937_, 5, v___x_2912_);
lean_ctor_set(v___x_2937_, 6, v___x_2936_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7, v___x_2924_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 1, v___x_2924_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 2, v___x_2924_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 3, v___x_2925_);
v___x_2938_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2912_);
lean_ctor_set(v___x_2938_, 1, v___x_2912_);
lean_ctor_set(v___x_2938_, 2, v___x_2912_);
lean_ctor_set(v___x_2938_, 3, v___x_2912_);
lean_ctor_set(v___x_2938_, 4, v___x_2927_);
lean_ctor_set(v___x_2938_, 5, v___x_2927_);
lean_ctor_set(v___x_2938_, 6, v___x_2927_);
lean_ctor_set(v___x_2938_, 7, v___x_2927_);
lean_ctor_set(v___x_2938_, 8, v___x_2927_);
lean_ctor_set(v___x_2938_, 9, v___x_2927_);
v___x_2939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2938_);
lean_ctor_set(v___x_2941_, 1, v___x_2939_);
lean_ctor_set(v___x_2941_, 2, v___x_2913_);
lean_ctor_set(v___x_2941_, 3, v___x_2932_);
lean_ctor_set(v___x_2941_, 4, v___x_2940_);
v___x_2942_ = lean_st_mk_ref(v___x_2941_);
v___x_2943_ = l_Lean_Meta_addSimpCongrTheorem(v_declName_2914_, v_attrKind_2916_, v_a_2923_, v___x_2937_, v___x_2942_, v___y_2917_, v___y_2918_);
lean_dec_ref_known(v___x_2937_, 7);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2952_; 
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2943_, 0);
lean_dec(v_unused_2953_);
v___x_2945_ = v___x_2943_;
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v___x_2943_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = lean_st_ref_get(v___x_2942_);
lean_dec(v___x_2942_);
lean_dec(v___x_2947_);
v___x_2948_ = lean_box(0);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
lean_dec(v___x_2942_);
return v___x_2943_;
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_declName_2914_);
lean_dec(v___x_2913_);
lean_dec(v___x_2912_);
v_a_2954_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2922_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2922_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v___x_2962_, lean_object* v___x_2963_, lean_object* v_declName_2964_, lean_object* v_stx_2965_, lean_object* v_attrKind_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
uint8_t v_attrKind_boxed_2970_; lean_object* v_res_2971_; 
v_attrKind_boxed_2970_ = lean_unbox(v_attrKind_2966_);
v_res_2971_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_2962_, v___x_2963_, v_declName_2964_, v_stx_2965_, v_attrKind_boxed_2970_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v_stx_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v_env_2977_; lean_object* v_options_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2976_ = lean_st_ref_get(v___y_2974_);
v_env_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_env_2977_);
lean_dec(v___x_2976_);
v_options_2978_ = lean_ctor_get(v___y_2973_, 2);
v___x_2979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_2980_ = lean_unsigned_to_nat(32u);
v___x_2981_ = lean_mk_empty_array_with_capacity(v___x_2980_);
lean_dec_ref(v___x_2981_);
v___x_2982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
lean_inc_ref(v_options_2978_);
v___x_2983_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2983_, 0, v_env_2977_);
lean_ctor_set(v___x_2983_, 1, v___x_2979_);
lean_ctor_set(v___x_2983_, 2, v___x_2982_);
lean_ctor_set(v___x_2983_, 3, v_options_2978_);
v___x_2984_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v_msgData_2972_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_ref_2995_; lean_object* v___x_2996_; lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
v_ref_2995_ = lean_ctor_get(v___y_2992_, 5);
v___x_2996_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msg_2991_, v___y_2992_, v___y_2993_);
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
lean_inc(v_ref_2995_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v_ref_2995_);
lean_ctor_set(v___x_3001_, 1, v_a_2997_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
lean_ctor_set(v___x_2999_, 0, v___x_3001_);
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
return v_res_3010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3013_ = l_Lean_stringToMessageData(v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object* v___x_3017_, lean_object* v_decl_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3023_ = l_Lean_MessageData_ofName(v___x_3017_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v___x_3026_, v___y_3019_, v___y_3020_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v___x_3028_, lean_object* v_decl_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_3028_, v_decl_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v_decl_3029_);
return v_res_3033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_unsigned_to_nat(3428004144u);
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3093_ = l_Lean_Name_num___override(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3097_ = l_Lean_Name_str___override(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3101_ = l_Lean_Name_str___override(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(2u);
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3104_ = l_Lean_Name_num___override(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3111_ = 0;
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3113_);
lean_ctor_set(v___x_3115_, 2, v___x_3112_);
lean_ctor_set_uint8(v___x_3115_, sizeof(void*)*3, v___x_3111_);
return v___x_3115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3116_; lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___f_3116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___f_3117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___f_3117_);
lean_ctor_set(v___x_3119_, 2, v___f_3116_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3122_ = l_Lean_registerBuiltinAttribute(v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3125_, lean_object* v_msg_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(v_00_u03b1_3131_, v_msg_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3141_ = l_Lean_addBuiltinDocString(v___x_3139_, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v_env_3147_; lean_object* v___x_3148_; lean_object* v_ext_3149_; lean_object* v_toEnvExtension_3150_; lean_object* v_asyncMode_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3146_ = lean_st_ref_get(v_a_3144_);
v_env_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3146_);
v___x_3148_ = l_Lean_Meta_congrExtension;
v_ext_3149_ = lean_ctor_get(v___x_3148_, 1);
v_toEnvExtension_3150_ = lean_ctor_get(v_ext_3149_, 0);
v_asyncMode_3151_ = lean_ctor_get(v_toEnvExtension_3150_, 2);
v___x_3152_ = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
v___x_3153_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3152_, v___x_3148_, v_env_3147_, v_asyncMode_3151_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3155_);
lean_dec(v_a_3155_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___boxed(lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Meta_getSimpCongrTheorems(v_a_3162_, v_a_3163_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
return v_res_3165_;
}
}
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedSimpCongrTheorems_default = _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorems_default);
l_Lean_Meta_instInhabitedSimpCongrTheorems = _init_l_Lean_Meta_instInhabitedSimpCongrTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorems);
res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_congrExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_congrExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
}
#ifdef __cplusplus
}
#endif

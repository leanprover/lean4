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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(uint8_t, lean_object*);
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
lean_dec_ref(v_x_46_);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref(v_x_46_);
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
lean_dec_ref(v_x_207_);
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
lean_dec_ref(v_x_378_);
v___x_383_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_382_);
return v___x_383_;
}
else
{
lean_object* v_head_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc(v_tail_381_);
v_head_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_head_384_);
lean_dec_ref(v_x_378_);
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
lean_dec_ref(v_x_423_);
return v_head_427_;
}
else
{
lean_object* v_head_428_; lean_object* v___x_429_; 
lean_inc(v_tail_426_);
v_head_428_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_head_428_);
lean_dec_ref(v_x_423_);
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
lean_dec_ref(v_x_496_);
v___x_501_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_500_);
return v___x_501_;
}
else
{
lean_object* v_head_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_tail_499_);
v_head_502_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_head_502_);
lean_dec_ref(v_x_496_);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; 
v___x_764_ = ((size_t)5ULL);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_shift_left(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_769_ = lean_usize_sub(v___x_768_, v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(lean_object* v_x_770_, size_t v_x_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v_es_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_794_; 
v_es_773_ = lean_ctor_get(v_x_770_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_794_ == 0)
{
v___x_775_ = v_x_770_;
v_isShared_776_ = v_isSharedCheck_794_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_es_773_);
lean_dec(v_x_770_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_794_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v_j_781_; lean_object* v___x_782_; 
v___x_777_ = lean_box(2);
v___x_778_ = ((size_t)5ULL);
v___x_779_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_780_ = lean_usize_land(v_x_771_, v___x_779_);
v_j_781_ = lean_usize_to_nat(v___x_780_);
v___x_782_ = lean_array_get(v___x_777_, v_es_773_, v_j_781_);
lean_dec(v_j_781_);
lean_dec_ref(v_es_773_);
switch(lean_obj_tag(v___x_782_))
{
case 0:
{
lean_object* v_key_783_; lean_object* v_val_784_; uint8_t v___x_785_; 
v_key_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_key_783_);
v_val_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_val_784_);
lean_dec_ref(v___x_782_);
v___x_785_ = lean_name_eq(v_x_772_, v_key_783_);
lean_dec(v_key_783_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v_val_784_);
lean_del_object(v___x_775_);
v___x_786_ = lean_box(0);
return v___x_786_;
}
else
{
lean_object* v___x_788_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 1);
lean_ctor_set(v___x_775_, 0, v_val_784_);
v___x_788_ = v___x_775_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_val_784_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
case 1:
{
lean_object* v_node_790_; size_t v___x_791_; 
lean_del_object(v___x_775_);
v_node_790_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_node_790_);
lean_dec_ref(v___x_782_);
v___x_791_ = lean_usize_shift_right(v_x_771_, v___x_778_);
v_x_770_ = v_node_790_;
v_x_771_ = v___x_791_;
goto _start;
}
default: 
{
lean_object* v___x_793_; 
lean_del_object(v___x_775_);
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
}
}
else
{
lean_object* v_ks_795_; lean_object* v_vs_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_ks_795_ = lean_ctor_get(v_x_770_, 0);
lean_inc_ref(v_ks_795_);
v_vs_796_ = lean_ctor_get(v_x_770_, 1);
lean_inc_ref(v_vs_796_);
lean_dec_ref(v_x_770_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_795_, v_vs_796_, v___x_797_, v_x_772_);
lean_dec_ref(v_vs_796_);
lean_dec_ref(v_ks_795_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
size_t v_x_337__boxed_802_; lean_object* v_res_803_; 
v_x_337__boxed_802_ = lean_unbox_usize(v_x_800_);
lean_dec(v_x_800_);
v_res_803_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_799_, v_x_337__boxed_802_, v_x_801_);
lean_dec(v_x_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
uint64_t v___y_807_; 
if (lean_obj_tag(v_x_805_) == 0)
{
uint64_t v___x_810_; 
v___x_810_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_807_ = v___x_810_;
goto v___jp_806_;
}
else
{
uint64_t v_hash_811_; 
v_hash_811_ = lean_ctor_get_uint64(v_x_805_, sizeof(void*)*2);
v___y_807_ = v_hash_811_;
goto v___jp_806_;
}
v___jp_806_:
{
size_t v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_uint64_to_usize(v___y_807_);
v___x_809_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_804_, v___x_808_, v_x_805_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg___boxed(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_812_, v_x_813_);
lean_dec(v_x_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
uint8_t v_stage_u2081_817_; 
v_stage_u2081_817_ = lean_ctor_get_uint8(v_x_815_, sizeof(void*)*2);
if (v_stage_u2081_817_ == 0)
{
lean_object* v_map_u2081_818_; lean_object* v_map_u2082_819_; lean_object* v___x_820_; 
v_map_u2081_818_ = lean_ctor_get(v_x_815_, 0);
lean_inc_ref(v_map_u2081_818_);
v_map_u2082_819_ = lean_ctor_get(v_x_815_, 1);
lean_inc_ref(v_map_u2082_819_);
lean_dec_ref(v_x_815_);
v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_map_u2082_819_, v_x_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_818_, v_x_816_);
lean_dec_ref(v_map_u2081_818_);
return v___x_821_;
}
else
{
lean_dec_ref(v_map_u2081_818_);
return v___x_820_;
}
}
else
{
lean_object* v_map_u2081_822_; lean_object* v___x_823_; 
v_map_u2081_822_ = lean_ctor_get(v_x_815_, 0);
lean_inc_ref(v_map_u2081_822_);
lean_dec_ref(v_x_815_);
v___x_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_822_, v_x_816_);
lean_dec_ref(v_map_u2081_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg___boxed(lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_x_824_, v_x_825_);
lean_dec(v_x_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get(lean_object* v_d_827_, lean_object* v_declName_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_d_827_, v_declName_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v___x_829_);
return v_val_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpCongrTheorems_get___boxed(lean_object* v_d_832_, lean_object* v_declName_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Meta_SimpCongrTheorems_get(v_d_832_, v_declName_833_);
lean_dec(v_declName_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_x_836_, v_x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___boxed(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(v_00_u03b2_839_, v_x_840_, v_x_841_);
lean_dec(v_x_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___boxed(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(v_00_u03b2_847_, v_x_848_, v_x_849_);
lean_dec(v_x_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(lean_object* v_00_u03b2_851_, lean_object* v_m_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_m_852_, v_a_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___boxed(lean_object* v_00_u03b2_855_, lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(v_00_u03b2_855_, v_m_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_m_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, size_t v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_860_, v_x_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
size_t v_x_466__boxed_868_; lean_object* v_res_869_; 
v_x_466__boxed_868_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_869_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(v_00_u03b2_864_, v_x_865_, v_x_466__boxed_868_, v_x_867_);
lean_dec(v_x_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_870_, lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_874_, lean_object* v_a_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(v_00_u03b2_874_, v_a_875_, v_x_876_);
lean_dec(v_x_876_);
lean_dec(v_a_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_heq_881_, lean_object* v_i_882_, lean_object* v_k_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_879_, v_vals_880_, v_i_882_, v_k_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_885_, lean_object* v_keys_886_, lean_object* v_vals_887_, lean_object* v_heq_888_, lean_object* v_i_889_, lean_object* v_k_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_885_, v_keys_886_, v_vals_887_, v_heq_888_, v_i_889_, v_k_890_);
lean_dec(v_k_890_);
lean_dec_ref(v_vals_887_);
lean_dec_ref(v_keys_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(lean_object* v_e_892_, lean_object* v_a_893_){
_start:
{
if (lean_obj_tag(v_a_893_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v_e_892_);
lean_ctor_set(v___x_894_, 1, v_a_893_);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v_priority_897_; lean_object* v_priority_898_; uint8_t v___x_899_; 
v_head_895_ = lean_ctor_get(v_a_893_, 0);
v_tail_896_ = lean_ctor_get(v_a_893_, 1);
v_priority_897_ = lean_ctor_get(v_head_895_, 3);
v_priority_898_ = lean_ctor_get(v_e_892_, 3);
v___x_899_ = lean_nat_dec_le(v_priority_897_, v_priority_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_tail_896_);
lean_inc(v_head_895_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_893_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_a_893_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_a_893_, 0);
lean_dec(v_unused_909_);
v___x_901_ = v_a_893_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_dec(v_a_893_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_892_, v_tail_896_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_head_895_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v_e_892_);
lean_ctor_set(v___x_910_, 1, v_a_893_);
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_913_) == 0)
{
lean_dec(v_b_912_);
lean_dec(v_a_911_);
return v_x_913_;
}
else
{
lean_object* v_key_914_; lean_object* v_value_915_; lean_object* v_tail_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_928_; 
v_key_914_ = lean_ctor_get(v_x_913_, 0);
v_value_915_ = lean_ctor_get(v_x_913_, 1);
v_tail_916_ = lean_ctor_get(v_x_913_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v_x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_918_ = v_x_913_;
v_isShared_919_ = v_isSharedCheck_928_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_tail_916_);
lean_inc(v_value_915_);
lean_inc(v_key_914_);
lean_dec(v_x_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_928_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = lean_name_eq(v_key_914_, v_a_911_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_911_, v_b_912_, v_tail_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 2, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_key_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_value_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v___x_926_; 
lean_dec(v_value_915_);
lean_dec(v_key_914_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_b_912_);
lean_ctor_set(v___x_918_, 0, v_a_911_);
v___x_926_ = v___x_918_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_911_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_b_912_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_tail_916_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
return v_x_929_;
}
else
{
lean_object* v_key_931_; lean_object* v_value_932_; lean_object* v_tail_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_959_; 
v_key_931_ = lean_ctor_get(v_x_930_, 0);
v_value_932_ = lean_ctor_get(v_x_930_, 1);
v_tail_933_ = lean_ctor_get(v_x_930_, 2);
v_isSharedCheck_959_ = !lean_is_exclusive(v_x_930_);
if (v_isSharedCheck_959_ == 0)
{
v___x_935_ = v_x_930_;
v_isShared_936_ = v_isSharedCheck_959_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_tail_933_);
lean_inc(v_value_932_);
lean_inc(v_key_931_);
lean_dec(v_x_930_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_959_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; uint64_t v___y_939_; 
v___x_937_ = lean_array_get_size(v_x_929_);
if (lean_obj_tag(v_key_931_) == 0)
{
uint64_t v___x_957_; 
v___x_957_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_939_ = v___x_957_;
goto v___jp_938_;
}
else
{
uint64_t v_hash_958_; 
v_hash_958_ = lean_ctor_get_uint64(v_key_931_, sizeof(void*)*2);
v___y_939_ = v_hash_958_;
goto v___jp_938_;
}
v___jp_938_:
{
uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v_fold_942_; uint64_t v___x_943_; uint64_t v___x_944_; uint64_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_940_ = 32ULL;
v___x_941_ = lean_uint64_shift_right(v___y_939_, v___x_940_);
v_fold_942_ = lean_uint64_xor(v___y_939_, v___x_941_);
v___x_943_ = 16ULL;
v___x_944_ = lean_uint64_shift_right(v_fold_942_, v___x_943_);
v___x_945_ = lean_uint64_xor(v_fold_942_, v___x_944_);
v___x_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = lean_usize_of_nat(v___x_937_);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_sub(v___x_947_, v___x_948_);
v___x_950_ = lean_usize_land(v___x_946_, v___x_949_);
v___x_951_ = lean_array_uget_borrowed(v_x_929_, v___x_950_);
lean_inc(v___x_951_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 2, v___x_951_);
v___x_953_ = v___x_935_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_key_931_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_value_932_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_951_);
v___x_953_ = v_reuseFailAlloc_956_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_array_uset(v_x_929_, v___x_950_, v___x_953_);
v_x_929_ = v___x_954_;
v_x_930_ = v_tail_933_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_960_, lean_object* v_source_961_, lean_object* v_target_962_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_source_961_);
v___x_964_ = lean_nat_dec_lt(v_i_960_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v_source_961_);
lean_dec(v_i_960_);
return v_target_962_;
}
else
{
lean_object* v_es_965_; lean_object* v___x_966_; lean_object* v_source_967_; lean_object* v_target_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_es_965_ = lean_array_fget(v_source_961_, v_i_960_);
v___x_966_ = lean_box(0);
v_source_967_ = lean_array_fset(v_source_961_, v_i_960_, v___x_966_);
v_target_968_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_962_, v_es_965_);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_add(v_i_960_, v___x_969_);
lean_dec(v_i_960_);
v_i_960_ = v___x_970_;
v_source_961_ = v_source_967_;
v_target_962_ = v_target_968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_data_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_nbuckets_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = lean_array_get_size(v_data_972_);
v___x_974_ = lean_unsigned_to_nat(2u);
v_nbuckets_975_ = lean_nat_mul(v___x_973_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_box(0);
v___x_978_ = lean_mk_array(v_nbuckets_975_, v___x_977_);
v___x_979_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_976_, v_data_972_, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_980_, lean_object* v_x_981_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
uint8_t v___x_982_; 
v___x_982_ = 0;
return v___x_982_;
}
else
{
lean_object* v_key_983_; lean_object* v_tail_984_; uint8_t v___x_985_; 
v_key_983_ = lean_ctor_get(v_x_981_, 0);
v_tail_984_ = lean_ctor_get(v_x_981_, 2);
v___x_985_ = lean_name_eq(v_key_983_, v_a_980_);
if (v___x_985_ == 0)
{
v_x_981_ = v_tail_984_;
goto _start;
}
else
{
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_987_, lean_object* v_x_988_){
_start:
{
uint8_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_987_, v_x_988_);
lean_dec(v_x_988_);
lean_dec(v_a_987_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(lean_object* v_m_991_, lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
lean_object* v_size_994_; lean_object* v_buckets_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1041_; 
v_size_994_ = lean_ctor_get(v_m_991_, 0);
v_buckets_995_ = lean_ctor_get(v_m_991_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_m_991_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_997_ = v_m_991_;
v_isShared_998_ = v_isSharedCheck_1041_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_buckets_995_);
lean_inc(v_size_994_);
lean_dec(v_m_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1041_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; uint64_t v___y_1001_; 
v___x_999_ = lean_array_get_size(v_buckets_995_);
if (lean_obj_tag(v_a_992_) == 0)
{
uint64_t v___x_1039_; 
v___x_1039_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_1001_ = v___x_1039_;
goto v___jp_1000_;
}
else
{
uint64_t v_hash_1040_; 
v_hash_1040_ = lean_ctor_get_uint64(v_a_992_, sizeof(void*)*2);
v___y_1001_ = v_hash_1040_;
goto v___jp_1000_;
}
v___jp_1000_:
{
uint64_t v___x_1002_; uint64_t v___x_1003_; uint64_t v_fold_1004_; uint64_t v___x_1005_; uint64_t v___x_1006_; uint64_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; lean_object* v_bkt_1013_; uint8_t v___x_1014_; 
v___x_1002_ = 32ULL;
v___x_1003_ = lean_uint64_shift_right(v___y_1001_, v___x_1002_);
v_fold_1004_ = lean_uint64_xor(v___y_1001_, v___x_1003_);
v___x_1005_ = 16ULL;
v___x_1006_ = lean_uint64_shift_right(v_fold_1004_, v___x_1005_);
v___x_1007_ = lean_uint64_xor(v_fold_1004_, v___x_1006_);
v___x_1008_ = lean_uint64_to_usize(v___x_1007_);
v___x_1009_ = lean_usize_of_nat(v___x_999_);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_sub(v___x_1009_, v___x_1010_);
v___x_1012_ = lean_usize_land(v___x_1008_, v___x_1011_);
v_bkt_1013_ = lean_array_uget_borrowed(v_buckets_995_, v___x_1012_);
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_992_, v_bkt_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v_size_x27_1016_; lean_object* v___x_1017_; lean_object* v_buckets_x27_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v_size_x27_1016_ = lean_nat_add(v_size_994_, v___x_1015_);
lean_dec(v_size_994_);
lean_inc(v_bkt_1013_);
v___x_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1017_, 0, v_a_992_);
lean_ctor_set(v___x_1017_, 1, v_b_993_);
lean_ctor_set(v___x_1017_, 2, v_bkt_1013_);
v_buckets_x27_1018_ = lean_array_uset(v_buckets_995_, v___x_1012_, v___x_1017_);
v___x_1019_ = lean_unsigned_to_nat(4u);
v___x_1020_ = lean_nat_mul(v_size_x27_1016_, v___x_1019_);
v___x_1021_ = lean_unsigned_to_nat(3u);
v___x_1022_ = lean_nat_div(v___x_1020_, v___x_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_array_get_size(v_buckets_x27_1018_);
v___x_1024_ = lean_nat_dec_le(v___x_1022_, v___x_1023_);
lean_dec(v___x_1022_);
if (v___x_1024_ == 0)
{
lean_object* v_val_1025_; lean_object* v___x_1027_; 
v_val_1025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1018_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_val_1025_);
lean_ctor_set(v___x_997_, 0, v_size_x27_1016_);
v___x_1027_ = v___x_997_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_size_x27_1016_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_val_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
lean_object* v___x_1030_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_buckets_x27_1018_);
lean_ctor_set(v___x_997_, 0, v_size_x27_1016_);
v___x_1030_ = v___x_997_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_size_x27_1016_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_buckets_x27_1018_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
else
{
lean_object* v___x_1032_; lean_object* v_buckets_x27_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_inc(v_bkt_1013_);
v___x_1032_ = lean_box(0);
v_buckets_x27_1033_ = lean_array_uset(v_buckets_995_, v___x_1012_, v___x_1032_);
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_992_, v_b_993_, v_bkt_1013_);
v___x_1035_ = lean_array_uset(v_buckets_x27_1033_, v___x_1012_, v___x_1034_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1035_);
v___x_1037_ = v___x_997_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_size_994_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_ks_1046_; lean_object* v_vs_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1071_; 
v_ks_1046_ = lean_ctor_get(v_x_1042_, 0);
v_vs_1047_ = lean_ctor_get(v_x_1042_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1049_ = v_x_1042_;
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_vs_1047_);
lean_inc(v_ks_1046_);
lean_dec(v_x_1042_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_array_get_size(v_ks_1046_);
v___x_1052_ = lean_nat_dec_lt(v_x_1043_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec(v_x_1043_);
v___x_1053_ = lean_array_push(v_ks_1046_, v_x_1044_);
v___x_1054_ = lean_array_push(v_vs_1047_, v_x_1045_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1054_);
lean_ctor_set(v___x_1049_, 0, v___x_1053_);
v___x_1056_ = v___x_1049_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
lean_object* v_k_x27_1058_; uint8_t v___x_1059_; 
v_k_x27_1058_ = lean_array_fget_borrowed(v_ks_1046_, v_x_1043_);
v___x_1059_ = lean_name_eq(v_x_1044_, v_k_x27_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; 
if (v_isShared_1050_ == 0)
{
v___x_1061_ = v___x_1049_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_ks_1046_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_vs_1047_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_x_1043_, v___x_1062_);
lean_dec(v_x_1043_);
v_x_1042_ = v___x_1061_;
v_x_1043_ = v___x_1063_;
goto _start;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1066_ = lean_array_fset(v_ks_1046_, v_x_1043_, v_x_1044_);
v___x_1067_ = lean_array_fset(v_vs_1047_, v_x_1043_, v_x_1045_);
lean_dec(v_x_1043_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1067_);
lean_ctor_set(v___x_1049_, 0, v___x_1066_);
v___x_1069_ = v___x_1049_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1072_, lean_object* v_k_1073_, lean_object* v_v_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_1072_, v___x_1075_, v_k_1073_, v_v_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1078_, size_t v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_es_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v_j_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_es_1083_ = lean_ctor_get(v_x_1078_, 0);
v___x_1084_ = ((size_t)5ULL);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1087_ = lean_usize_land(v_x_1079_, v___x_1086_);
v_j_1088_ = lean_usize_to_nat(v___x_1087_);
v___x_1089_ = lean_array_get_size(v_es_1083_);
v___x_1090_ = lean_nat_dec_lt(v_j_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_dec(v_j_1088_);
lean_dec(v_x_1082_);
lean_dec(v_x_1081_);
return v_x_1078_;
}
else
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1127_; 
lean_inc_ref(v_es_1083_);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_x_1078_, 0);
lean_dec(v_unused_1128_);
v___x_1092_ = v_x_1078_;
v_isShared_1093_ = v_isSharedCheck_1127_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_x_1078_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1127_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_v_1094_; lean_object* v___x_1095_; lean_object* v_xs_x27_1096_; lean_object* v___y_1098_; 
v_v_1094_ = lean_array_fget(v_es_1083_, v_j_1088_);
v___x_1095_ = lean_box(0);
v_xs_x27_1096_ = lean_array_fset(v_es_1083_, v_j_1088_, v___x_1095_);
switch(lean_obj_tag(v_v_1094_))
{
case 0:
{
lean_object* v_key_1103_; lean_object* v_val_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_key_1103_ = lean_ctor_get(v_v_1094_, 0);
v_val_1104_ = lean_ctor_get(v_v_1094_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_v_1094_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v_v_1094_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_val_1104_);
lean_inc(v_key_1103_);
lean_dec(v_v_1094_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_name_eq(v_x_1081_, v_key_1103_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_del_object(v___x_1106_);
v___x_1109_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1103_, v_val_1104_, v_x_1081_, v_x_1082_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
v___y_1098_ = v___x_1110_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1112_; 
lean_dec(v_val_1104_);
lean_dec(v_key_1103_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v_x_1082_);
lean_ctor_set(v___x_1106_, 0, v_x_1081_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_x_1081_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_x_1082_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v___y_1098_ = v___x_1112_;
goto v___jp_1097_;
}
}
}
}
case 1:
{
lean_object* v_node_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1125_; 
v_node_1115_ = lean_ctor_get(v_v_1094_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_v_1094_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1117_ = v_v_1094_;
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_node_1115_);
lean_dec(v_v_1094_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1119_ = lean_usize_shift_right(v_x_1079_, v___x_1084_);
v___x_1120_ = lean_usize_add(v_x_1080_, v___x_1085_);
v___x_1121_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_node_1115_, v___x_1119_, v___x_1120_, v_x_1081_, v_x_1082_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v___y_1098_ = v___x_1123_;
goto v___jp_1097_;
}
}
}
default: 
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_x_1081_);
lean_ctor_set(v___x_1126_, 1, v_x_1082_);
v___y_1098_ = v___x_1126_;
goto v___jp_1097_;
}
}
v___jp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_array_fset(v_xs_x27_1096_, v_j_1088_, v___y_1098_);
lean_dec(v_j_1088_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1099_);
v___x_1101_ = v___x_1092_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_ks_1129_; lean_object* v_vs_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1150_; 
v_ks_1129_ = lean_ctor_get(v_x_1078_, 0);
v_vs_1130_ = lean_ctor_get(v_x_1078_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1132_ = v_x_1078_;
v_isShared_1133_ = v_isSharedCheck_1150_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_vs_1130_);
lean_inc(v_ks_1129_);
lean_dec(v_x_1078_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1150_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_ks_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_vs_1130_);
v___x_1135_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v_newNode_1136_; uint8_t v___y_1138_; size_t v___x_1144_; uint8_t v___x_1145_; 
v_newNode_1136_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1135_, v_x_1081_, v_x_1082_);
v___x_1144_ = ((size_t)7ULL);
v___x_1145_ = lean_usize_dec_le(v___x_1144_, v_x_1080_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1136_);
v___x_1147_ = lean_unsigned_to_nat(4u);
v___x_1148_ = lean_nat_dec_lt(v___x_1146_, v___x_1147_);
lean_dec(v___x_1146_);
v___y_1138_ = v___x_1148_;
goto v___jp_1137_;
}
else
{
v___y_1138_ = v___x_1145_;
goto v___jp_1137_;
}
v___jp_1137_:
{
if (v___y_1138_ == 0)
{
lean_object* v_ks_1139_; lean_object* v_vs_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_ks_1139_ = lean_ctor_get(v_newNode_1136_, 0);
lean_inc_ref(v_ks_1139_);
v_vs_1140_ = lean_ctor_get(v_newNode_1136_, 1);
lean_inc_ref(v_vs_1140_);
lean_dec_ref(v_newNode_1136_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1080_, v_ks_1139_, v_vs_1140_, v___x_1141_, v___x_1142_);
lean_dec_ref(v_vs_1140_);
lean_dec_ref(v_ks_1139_);
return v___x_1143_;
}
else
{
return v_newNode_1136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_i_1154_, lean_object* v_entries_1155_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_array_get_size(v_keys_1152_);
v___x_1157_ = lean_nat_dec_lt(v_i_1154_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v_i_1154_);
return v_entries_1155_;
}
else
{
lean_object* v_k_1158_; lean_object* v_v_1159_; uint64_t v___y_1161_; 
v_k_1158_ = lean_array_fget_borrowed(v_keys_1152_, v_i_1154_);
v_v_1159_ = lean_array_fget_borrowed(v_vals_1153_, v_i_1154_);
if (lean_obj_tag(v_k_1158_) == 0)
{
uint64_t v___x_1172_; 
v___x_1172_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_1161_ = v___x_1172_;
goto v___jp_1160_;
}
else
{
uint64_t v_hash_1173_; 
v_hash_1173_ = lean_ctor_get_uint64(v_k_1158_, sizeof(void*)*2);
v___y_1161_ = v_hash_1173_;
goto v___jp_1160_;
}
v___jp_1160_:
{
size_t v_h_1162_; size_t v___x_1163_; lean_object* v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; size_t v_h_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_h_1162_ = lean_uint64_to_usize(v___y_1161_);
v___x_1163_ = ((size_t)5ULL);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_sub(v_depth_1151_, v___x_1165_);
v___x_1167_ = lean_usize_mul(v___x_1163_, v___x_1166_);
v_h_1168_ = lean_usize_shift_right(v_h_1162_, v___x_1167_);
v___x_1169_ = lean_nat_add(v_i_1154_, v___x_1164_);
lean_dec(v_i_1154_);
lean_inc(v_v_1159_);
lean_inc(v_k_1158_);
v___x_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_entries_1155_, v_h_1168_, v_depth_1151_, v_k_1158_, v_v_1159_);
v_i_1154_ = v___x_1169_;
v_entries_1155_ = v___x_1170_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1174_, lean_object* v_keys_1175_, lean_object* v_vals_1176_, lean_object* v_i_1177_, lean_object* v_entries_1178_){
_start:
{
size_t v_depth_boxed_1179_; lean_object* v_res_1180_; 
v_depth_boxed_1179_ = lean_unbox_usize(v_depth_1174_);
lean_dec(v_depth_1174_);
v_res_1180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1179_, v_keys_1175_, v_vals_1176_, v_i_1177_, v_entries_1178_);
lean_dec_ref(v_vals_1176_);
lean_dec_ref(v_keys_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
size_t v_x_1056__boxed_1186_; size_t v_x_1057__boxed_1187_; lean_object* v_res_1188_; 
v_x_1056__boxed_1186_ = lean_unbox_usize(v_x_1182_);
lean_dec(v_x_1182_);
v_x_1057__boxed_1187_ = lean_unbox_usize(v_x_1183_);
lean_dec(v_x_1183_);
v_res_1188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1181_, v_x_1056__boxed_1186_, v_x_1057__boxed_1187_, v_x_1184_, v_x_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
uint64_t v___y_1193_; 
if (lean_obj_tag(v_x_1190_) == 0)
{
uint64_t v___x_1197_; 
v___x_1197_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
v___y_1193_ = v___x_1197_;
goto v___jp_1192_;
}
else
{
uint64_t v_hash_1198_; 
v_hash_1198_ = lean_ctor_get_uint64(v_x_1190_, sizeof(void*)*2);
v___y_1193_ = v_hash_1198_;
goto v___jp_1192_;
}
v___jp_1192_:
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_uint64_to_usize(v___y_1193_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1189_, v___x_1194_, v___x_1195_, v_x_1190_, v_x_1191_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
uint8_t v_stage_u2081_1202_; 
v_stage_u2081_1202_ = lean_ctor_get_uint8(v_x_1199_, sizeof(void*)*2);
if (v_stage_u2081_1202_ == 0)
{
lean_object* v_map_u2081_1203_; lean_object* v_map_u2082_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_map_u2081_1203_ = lean_ctor_get(v_x_1199_, 0);
v_map_u2082_1204_ = lean_ctor_get(v_x_1199_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v_x_1199_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_map_u2082_1204_);
lean_inc(v_map_u2081_1203_);
lean_dec(v_x_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_map_u2082_1204_, v_x_1200_, v_x_1201_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_map_u2081_1203_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*2, v_stage_u2081_1202_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_map_u2081_1213_; lean_object* v_map_u2082_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_map_u2081_1213_ = lean_ctor_get(v_x_1199_, 0);
v_map_u2082_1214_ = lean_ctor_get(v_x_1199_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v_x_1199_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_map_u2082_1214_);
lean_inc(v_map_u2081_1213_);
lean_dec(v_x_1199_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_map_u2081_1213_, v_x_1200_, v_x_1201_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_map_u2082_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, sizeof(void*)*2, v_stage_u2081_1202_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheoremEntry(lean_object* v_d_1223_, lean_object* v_e_1224_){
_start:
{
lean_object* v_funName_1225_; lean_object* v___x_1226_; 
v_funName_1225_ = lean_ctor_get(v_e_1224_, 1);
lean_inc(v_funName_1225_);
lean_inc_ref(v_d_1223_);
v___x_1226_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(v_d_1223_, v_funName_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_e_1224_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_d_1223_, v_funName_1225_, v___x_1228_);
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_val_1230_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v___x_1226_);
v___x_1231_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_1224_, v_val_1230_);
v___x_1232_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_d_1223_, v_funName_1225_, v___x_1231_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0(lean_object* v_00_u03b2_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(v_x_1234_, v_x_1235_, v_x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0(lean_object* v_00_u03b2_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_x_1239_, v_x_1240_, v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_m_1244_, v_a_1245_, v_b_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, size_t v_x_1250_, size_t v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_1249_, v_x_1250_, v_x_1251_, v_x_1252_, v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
size_t v_x_1315__boxed_1261_; size_t v_x_1316__boxed_1262_; lean_object* v_res_1263_; 
v_x_1315__boxed_1261_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_x_1316__boxed_1262_ = lean_unbox_usize(v_x_1258_);
lean_dec(v_x_1258_);
v_res_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(v_00_u03b2_1255_, v_x_1256_, v_x_1315__boxed_1261_, v_x_1316__boxed_1262_, v_x_1259_, v_x_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1264_, lean_object* v_a_1265_, lean_object* v_x_1266_){
_start:
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(v_00_u03b2_1268_, v_a_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec(v_a_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1273_, lean_object* v_data_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_data_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1276_, lean_object* v_a_1277_, lean_object* v_b_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_1277_, v_b_1278_, v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1281_, lean_object* v_n_1282_, lean_object* v_k_1283_, lean_object* v_v_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1282_, v_k_1283_, v_v_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1286_, size_t v_depth_1287_, lean_object* v_keys_1288_, lean_object* v_vals_1289_, lean_object* v_heq_1290_, lean_object* v_i_1291_, lean_object* v_entries_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1287_, v_keys_1288_, v_vals_1289_, v_i_1291_, v_entries_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_depth_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_entries_1300_){
_start:
{
size_t v_depth_boxed_1301_; lean_object* v_res_1302_; 
v_depth_boxed_1301_ = lean_unbox_usize(v_depth_1295_);
lean_dec(v_depth_1295_);
v_res_1302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1294_, v_depth_boxed_1301_, v_keys_1296_, v_vals_1297_, v_heq_1298_, v_i_1299_, v_entries_1300_);
lean_dec_ref(v_vals_1297_);
lean_dec_ref(v_keys_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1303_, lean_object* v_i_1304_, lean_object* v_source_1305_, lean_object* v_target_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_1304_, v_source_1305_, v_target_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1309_, v_x_1310_, v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_1315_, v_x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_1318_){
_start:
{
uint8_t v_stage_u2081_1319_; 
v_stage_u2081_1319_ = lean_ctor_get_uint8(v_m_1318_, sizeof(void*)*2);
if (v_stage_u2081_1319_ == 0)
{
return v_m_1318_;
}
else
{
lean_object* v_map_u2081_1320_; lean_object* v_map_u2082_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_map_u2081_1320_ = lean_ctor_get(v_m_1318_, 0);
v_map_u2082_1321_ = lean_ctor_get(v_m_1318_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_m_1318_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v_m_1318_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_map_u2082_1321_);
lean_inc(v_map_u2081_1320_);
lean_dec(v_m_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = 0;
if (v_isShared_1324_ == 0)
{
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_map_u2081_1320_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_map_u2082_1321_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*2, v___x_1325_);
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1330_, lean_object* v_m_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(v_m_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(uint8_t v_x_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___y_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object* v_x_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_x_80__boxed_1338_; lean_object* v_res_1339_; 
v_x_80__boxed_1338_ = lean_unbox(v_x_1336_);
v_res_1339_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(v_x_80__boxed_1338_, v___y_1337_);
return v_res_1339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___f_1350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___f_1351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1352_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4, &l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once, _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4);
v___x_1353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_));
v___x_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1352_);
lean_ctor_set(v___x_1355_, 3, v___f_1351_);
lean_ctor_set(v___x_1355_, 4, v___f_1350_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_);
v___x_1358_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
return v_res_1360_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(lean_object* v_k_1361_, lean_object* v_t_1362_){
_start:
{
if (lean_obj_tag(v_t_1362_) == 0)
{
lean_object* v_k_1363_; lean_object* v_l_1364_; lean_object* v_r_1365_; uint8_t v___x_1366_; 
v_k_1363_ = lean_ctor_get(v_t_1362_, 1);
v_l_1364_ = lean_ctor_get(v_t_1362_, 3);
v_r_1365_ = lean_ctor_get(v_t_1362_, 4);
v___x_1366_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1361_, v_k_1363_);
switch(v___x_1366_)
{
case 0:
{
v_t_1362_ = v_l_1364_;
goto _start;
}
case 1:
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
return v___x_1368_;
}
default: 
{
v_t_1362_ = v_r_1365_;
goto _start;
}
}
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg___boxed(lean_object* v_k_1371_, lean_object* v_t_1372_){
_start:
{
uint8_t v_res_1373_; lean_object* v_r_1374_; 
v_res_1373_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_1371_, v_t_1372_);
lean_dec(v_t_1372_);
lean_dec(v_k_1371_);
v_r_1374_ = lean_box(v_res_1373_);
return v_r_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(lean_object* v_mvarSet_1375_, lean_object* v_e_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_Expr_isMVar(v_e_1376_);
if (v___x_1377_ == 0)
{
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = l_Lean_Expr_mvarId_x21(v_e_1376_);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1378_, v_mvarSet_1375_);
lean_dec(v___x_1378_);
if (v___x_1379_ == 0)
{
return v___x_1377_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = 0;
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(lean_object* v_mvarSet_1381_, lean_object* v_e_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(v_mvarSet_1381_, v_e_1382_);
lean_dec_ref(v_e_1382_);
lean_dec(v_mvarSet_1381_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(lean_object* v_t_1385_, lean_object* v_mvarSet_1386_){
_start:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1387_, 0, v_mvarSet_1386_);
v___x_1388_ = lean_find_expr(v___f_1387_, v_t_1385_);
lean_dec_ref(v___f_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
uint8_t v___x_1389_; 
v___x_1389_ = 1;
return v___x_1389_;
}
else
{
uint8_t v___x_1390_; 
lean_dec_ref(v___x_1388_);
v___x_1390_ = 0;
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(lean_object* v_t_1391_, lean_object* v_mvarSet_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_t_1391_, v_mvarSet_1392_);
lean_dec_ref(v_t_1391_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(lean_object* v_00_u03b2_1395_, lean_object* v_k_1396_, lean_object* v_t_1397_){
_start:
{
uint8_t v___x_1398_; 
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_1396_, v_t_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___boxed(lean_object* v_00_u03b2_1399_, lean_object* v_k_1400_, lean_object* v_t_1401_){
_start:
{
uint8_t v_res_1402_; lean_object* v_r_1403_; 
v_res_1402_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(v_00_u03b2_1399_, v_k_1400_, v_t_1401_);
lean_dec(v_t_1401_);
lean_dec(v_k_1400_);
v_r_1403_ = lean_box(v_res_1402_);
return v_r_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(lean_object* v_k_1404_, lean_object* v_b_1405_, lean_object* v_c_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
v___x_1412_ = lean_apply_7(v_k_1404_, v_b_1405_, v_c_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, lean_box(0));
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed(lean_object* v_k_1413_, lean_object* v_b_1414_, lean_object* v_c_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(v_k_1413_, v_b_1414_, v_c_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(lean_object* v_type_1422_, lean_object* v_k_1423_, uint8_t v_cleanupAnnotations_1424_, uint8_t v_whnfType_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___f_1431_; lean_object* v___x_1432_; 
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1431_, 0, v_k_1423_);
v___x_1432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1422_, v___f_1431_, v_cleanupAnnotations_1424_, v_whnfType_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1432_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1432_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___boxed(lean_object* v_type_1449_, lean_object* v_k_1450_, lean_object* v_cleanupAnnotations_1451_, lean_object* v_whnfType_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1458_; uint8_t v_whnfType_boxed_1459_; lean_object* v_res_1460_; 
v_cleanupAnnotations_boxed_1458_ = lean_unbox(v_cleanupAnnotations_1451_);
v_whnfType_boxed_1459_ = lean_unbox(v_whnfType_1452_);
v_res_1460_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_type_1449_, v_k_1450_, v_cleanupAnnotations_boxed_1458_, v_whnfType_boxed_1459_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(lean_object* v_00_u03b1_1461_, lean_object* v_type_1462_, lean_object* v_k_1463_, uint8_t v_cleanupAnnotations_1464_, uint8_t v_whnfType_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_type_1462_, v_k_1463_, v_cleanupAnnotations_1464_, v_whnfType_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(lean_object* v_00_u03b1_1472_, lean_object* v_type_1473_, lean_object* v_k_1474_, lean_object* v_cleanupAnnotations_1475_, lean_object* v_whnfType_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1482_; uint8_t v_whnfType_boxed_1483_; lean_object* v_res_1484_; 
v_cleanupAnnotations_boxed_1482_ = lean_unbox(v_cleanupAnnotations_1475_);
v_whnfType_boxed_1483_ = lean_unbox(v_whnfType_1476_);
v_res_1484_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(v_00_u03b1_1472_, v_type_1473_, v_k_1474_, v_cleanupAnnotations_boxed_1482_, v_whnfType_boxed_1483_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(lean_object* v_msgData_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v_env_1492_; lean_object* v___x_1493_; lean_object* v_mctx_1494_; lean_object* v_lctx_1495_; lean_object* v_options_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1491_ = lean_st_ref_get(v___y_1489_);
v_env_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc_ref(v_env_1492_);
lean_dec(v___x_1491_);
v___x_1493_ = lean_st_ref_get(v___y_1487_);
v_mctx_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_mctx_1494_);
lean_dec(v___x_1493_);
v_lctx_1495_ = lean_ctor_get(v___y_1486_, 2);
v_options_1496_ = lean_ctor_get(v___y_1488_, 2);
lean_inc_ref(v_options_1496_);
lean_inc_ref(v_lctx_1495_);
v___x_1497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1497_, 0, v_env_1492_);
lean_ctor_set(v___x_1497_, 1, v_mctx_1494_);
lean_ctor_set(v___x_1497_, 2, v_lctx_1495_);
lean_ctor_set(v___x_1497_, 3, v_options_1496_);
v___x_1498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_msgData_1485_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5___boxed(lean_object* v_msgData_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msgData_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_ref_1513_; lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1523_; 
v_ref_1513_ = lean_ctor_get(v___y_1510_, 5);
v___x_1514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msg_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_inc(v_ref_1513_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_ref_1513_);
lean_ctor_set(v___x_1519_, 1, v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
lean_ctor_set(v___x_1517_, 0, v___x_1519_);
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg___boxed(lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(lean_object* v___x_1537_, lean_object* v_snd_1538_, lean_object* v_as_1539_, size_t v_sz_1540_, size_t v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_a_1549_; uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_lt(v_i_1541_, v_sz_1540_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v_snd_1538_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_b_1542_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v_a_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_box(0);
v_a_1556_ = lean_array_uget_borrowed(v_as_1539_, v_i_1541_);
v___x_1557_ = l_Lean_Expr_isFVar(v_a_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1558_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v___x_1537_, v___x_1559_);
v___x_1561_ = l_Nat_reprFast(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
v___x_1563_ = l_Lean_MessageData_ofFormat(v___x_1562_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1558_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_inc_ref(v_snd_1538_);
v___x_1567_ = l_Lean_indentExpr(v_snd_1538_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1568_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec_ref(v___x_1569_);
v_a_1549_ = v___x_1555_;
goto v___jp_1548_;
}
else
{
lean_dec_ref(v_snd_1538_);
return v___x_1569_;
}
}
else
{
v_a_1549_ = v___x_1555_;
goto v___jp_1548_;
}
}
v___jp_1548_:
{
size_t v___x_1550_; size_t v___x_1551_; 
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_add(v_i_1541_, v___x_1550_);
v_i_1541_ = v___x_1551_;
v_b_1542_ = v_a_1549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(lean_object* v___x_1570_, lean_object* v_snd_1571_, lean_object* v_as_1572_, lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_b_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
size_t v_sz_boxed_1581_; size_t v_i_boxed_1582_; lean_object* v_res_1583_; 
v_sz_boxed_1581_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1582_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v___x_1570_, v_snd_1571_, v_as_1572_, v_sz_boxed_1581_, v_i_boxed_1582_, v_b_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v_as_1572_);
lean_dec(v___x_1570_);
return v_res_1583_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_as_1595_, size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec(v___x_1593_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_b_1598_);
return v___x_1611_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_array_uget_borrowed(v_as_1595_, v_i_1597_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v_a_1612_);
v___x_1613_ = lean_infer_type(v_a_1612_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; uint8_t v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
lean_inc(v___x_1593_);
v___x_1615_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_a_1614_, v___x_1593_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1);
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_b_1598_, v___x_1617_);
v___x_1619_ = l_Nat_reprFast(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofFormat(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1616_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_nat_add(v___x_1594_, v___x_1617_);
v___x_1626_ = l_Nat_reprFast(v___x_1625_);
v___x_1627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = l_Lean_MessageData_ofFormat(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1624_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_indentExpr(v_a_1614_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1633_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref(v___x_1634_);
goto v___jp_1604_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_b_1598_);
lean_dec(v___x_1593_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_dec(v_a_1614_);
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_b_1598_);
lean_dec(v___x_1593_);
v_a_1643_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1613_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1613_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
v___jp_1604_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = lean_nat_add(v_b_1598_, v___x_1605_);
lean_dec(v_b_1598_);
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1597_, v___x_1607_);
v_i_1597_ = v___x_1608_;
v_b_1598_ = v___x_1606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v_as_1653_, lean_object* v_sz_1654_, lean_object* v_i_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
size_t v_sz_boxed_1662_; size_t v_i_boxed_1663_; lean_object* v_res_1664_; 
v_sz_boxed_1662_ = lean_unbox_usize(v_sz_1654_);
lean_dec(v_sz_1654_);
v_i_boxed_1663_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v___x_1651_, v___x_1652_, v_as_1653_, v_sz_boxed_1662_, v_i_boxed_1663_, v_b_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_as_1653_);
lean_dec(v___x_1652_);
return v_res_1664_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1665_; lean_object* v_dummy_1666_; 
v___x_1665_ = lean_box(0);
v_dummy_1666_ = l_Lean_Expr_sort___override(v___x_1665_);
return v_dummy_1666_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1));
v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3));
v___x_1672_ = l_Lean_stringToMessageData(v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(lean_object* v_fst_1682_, lean_object* v_fst_1683_, lean_object* v___x_1684_, lean_object* v_ys_1685_, lean_object* v_xType_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1756_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8));
v___x_1815_ = lean_unsigned_to_nat(3u);
v___x_1816_ = l_Lean_Expr_isAppOfArity(v_xType_1686_, v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10));
v___x_1818_ = lean_unsigned_to_nat(2u);
v___x_1819_ = l_Lean_Expr_isAppOfArity(v_xType_1686_, v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v___x_1684_);
lean_dec(v_fst_1683_);
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_Expr_appFn_x21(v_xType_1686_);
v___x_1823_ = l_Lean_Expr_appArg_x21(v___x_1822_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = l_Lean_Expr_appArg_x21(v_xType_1686_);
v_fst_1780_ = v___x_1823_;
v_snd_1781_ = v___x_1824_;
goto v___jp_1779_;
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = l_Lean_Expr_appFn_x21(v_xType_1686_);
v___x_1826_ = l_Lean_Expr_appArg_x21(v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = l_Lean_Expr_appArg_x21(v_xType_1686_);
v_fst_1780_ = v___x_1826_;
v_snd_1781_ = v___x_1827_;
goto v___jp_1779_;
}
v___jp_1692_:
{
lean_object* v_dummy_1699_; lean_object* v_nargs_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v_dummy_1699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_1700_ = l_Lean_Expr_getAppNumArgs(v___y_1693_);
lean_inc(v_nargs_1700_);
v___x_1701_ = lean_mk_array(v_nargs_1700_, v_dummy_1699_);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_sub(v_nargs_1700_, v___x_1702_);
lean_dec(v_nargs_1700_);
lean_inc_ref(v___y_1693_);
v___x_1704_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1693_, v___x_1701_, v___x_1703_);
v___x_1705_ = lean_box(0);
v_sz_1706_ = lean_array_size(v___x_1704_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v_fst_1682_, v___y_1693_, v___x_1704_, v_sz_1706_, v___x_1707_, v___x_1705_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec_ref(v___x_1704_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1708_, 0);
lean_dec(v_unused_1717_);
v___x_1710_ = v___x_1708_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v___x_1708_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___y_1694_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___y_1694_);
v_a_1718_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1708_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1708_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
v___jp_1726_:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = l_Lean_Expr_mvarId_x21(v___y_1728_);
v___x_1734_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1733_, v_fst_1683_);
lean_dec(v_fst_1683_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
v___y_1693_ = v___y_1727_;
v___y_1694_ = v___y_1728_;
v___y_1695_ = v___y_1729_;
v___y_1696_ = v___y_1730_;
v___y_1697_ = v___y_1731_;
v___y_1698_ = v___y_1732_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_fst_1682_, v___x_1736_);
v___x_1738_ = l_Nat_reprFast(v___x_1737_);
v___x_1739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___x_1740_ = l_Lean_MessageData_ofFormat(v___x_1739_);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1735_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
lean_inc_ref(v___y_1727_);
v___x_1744_ = l_Lean_indentExpr(v___y_1727_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1745_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_dec_ref(v___x_1746_);
v___y_1693_ = v___y_1727_;
v___y_1694_ = v___y_1728_;
v___y_1695_ = v___y_1729_;
v___y_1696_ = v___y_1730_;
v___y_1697_ = v___y_1731_;
v___y_1698_ = v___y_1732_;
goto v___jp_1692_;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v___y_1728_);
lean_dec_ref(v___y_1727_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
v___jp_1755_:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = l_Lean_Expr_getAppFn(v___y_1756_);
v___x_1758_ = l_Lean_Expr_isMVar(v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_fst_1682_, v___x_1760_);
v___x_1762_ = l_Nat_reprFast(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
v___x_1764_ = l_Lean_MessageData_ofFormat(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1759_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_inc_ref(v___y_1756_);
v___x_1768_ = l_Lean_indentExpr(v___y_1756_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1769_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref(v___x_1770_);
v___y_1727_ = v___y_1756_;
v___y_1728_ = v___x_1757_;
v___y_1729_ = v___y_1687_;
v___y_1730_ = v___y_1688_;
v___y_1731_ = v___y_1689_;
v___y_1732_ = v___y_1690_;
goto v___jp_1726_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___x_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v_fst_1683_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
v___y_1727_ = v___y_1756_;
v___y_1728_ = v___x_1757_;
v___y_1729_ = v___y_1687_;
v___y_1730_ = v___y_1688_;
v___y_1731_ = v___y_1689_;
v___y_1732_ = v___y_1690_;
goto v___jp_1726_;
}
}
v___jp_1779_:
{
size_t v_sz_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v_sz_1782_ = lean_array_size(v_ys_1685_);
v___x_1783_ = ((size_t)0ULL);
lean_inc(v_fst_1683_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v_fst_1683_, v_fst_1682_, v_ys_1685_, v_sz_1782_, v___x_1783_, v___x_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1784_) == 0)
{
uint8_t v___x_1785_; 
lean_dec_ref(v___x_1784_);
lean_inc(v_fst_1683_);
v___x_1785_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_fst_1780_, v_fst_1683_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_fst_1682_, v___x_1787_);
v___x_1789_ = l_Nat_reprFast(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___x_1791_ = l_Lean_MessageData_ofFormat(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1786_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_indentExpr(v_fst_1780_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_1796_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref(v___x_1797_);
v___y_1756_ = v_snd_1781_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v_snd_1781_);
lean_dec(v_fst_1683_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
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
else
{
lean_dec_ref(v_fst_1780_);
v___y_1756_ = v_snd_1781_;
goto v___jp_1755_;
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref(v_snd_1781_);
lean_dec_ref(v_fst_1780_);
lean_dec(v_fst_1683_);
v_a_1806_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1784_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1784_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(lean_object* v_fst_1828_, lean_object* v_fst_1829_, lean_object* v___x_1830_, lean_object* v_ys_1831_, lean_object* v_xType_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(v_fst_1828_, v_fst_1829_, v___x_1830_, v_ys_1831_, v_xType_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v_xType_1832_);
lean_dec_ref(v_ys_1831_);
lean_dec(v_fst_1828_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(lean_object* v_as_1839_, size_t v_sz_1840_, size_t v_i_1841_, lean_object* v_b_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_lt(v_i_1841_, v_sz_1840_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_b_1842_);
return v___x_1849_;
}
else
{
lean_object* v_snd_1850_; lean_object* v_snd_1851_; lean_object* v_snd_1852_; lean_object* v_fst_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1948_; 
v_snd_1850_ = lean_ctor_get(v_b_1842_, 1);
lean_inc(v_snd_1850_);
v_snd_1851_ = lean_ctor_get(v_snd_1850_, 1);
lean_inc(v_snd_1851_);
v_snd_1852_ = lean_ctor_get(v_snd_1851_, 1);
lean_inc(v_snd_1852_);
v_fst_1853_ = lean_ctor_get(v_b_1842_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_b_1842_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v_b_1842_, 1);
lean_dec(v_unused_1949_);
v___x_1855_ = v_b_1842_;
v_isShared_1856_ = v_isSharedCheck_1948_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_fst_1853_);
lean_dec(v_b_1842_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1948_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1946_; 
v_fst_1857_ = lean_ctor_get(v_snd_1850_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_snd_1850_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_snd_1850_, 1);
lean_dec(v_unused_1947_);
v___x_1859_ = v_snd_1850_;
v_isShared_1860_ = v_isSharedCheck_1946_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_fst_1857_);
lean_dec(v_snd_1850_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1946_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_fst_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1944_; 
v_fst_1861_ = lean_ctor_get(v_snd_1851_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_snd_1851_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v_snd_1851_, 1);
lean_dec(v_unused_1945_);
v___x_1863_ = v_snd_1851_;
v_isShared_1864_ = v_isSharedCheck_1944_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_fst_1861_);
lean_dec(v_snd_1851_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1944_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_array_1865_; lean_object* v_start_1866_; lean_object* v_stop_1867_; uint8_t v___x_1868_; 
v_array_1865_ = lean_ctor_get(v_snd_1852_, 0);
v_start_1866_ = lean_ctor_get(v_snd_1852_, 1);
v_stop_1867_ = lean_ctor_get(v_snd_1852_, 2);
v___x_1868_ = lean_nat_dec_lt(v_start_1866_, v_stop_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; 
if (v_isShared_1864_ == 0)
{
v___x_1870_ = v___x_1863_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_fst_1861_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_snd_1852_);
v___x_1870_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1872_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1870_);
v___x_1872_ = v___x_1859_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_fst_1857_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1872_);
v___x_1874_ = v___x_1855_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_fst_1853_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
}
}
else
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1940_; 
lean_inc(v_stop_1867_);
lean_inc(v_start_1866_);
lean_inc_ref(v_array_1865_);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_snd_1852_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; lean_object* v_unused_1942_; lean_object* v_unused_1943_; 
v_unused_1941_ = lean_ctor_get(v_snd_1852_, 2);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v_snd_1852_, 1);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_snd_1852_, 0);
lean_dec(v_unused_1943_);
v___x_1880_ = v_snd_1852_;
v_isShared_1881_ = v_isSharedCheck_1940_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v_snd_1852_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1940_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___f_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1882_ = lean_unsigned_to_nat(0u);
v_a_1883_ = lean_array_uget_borrowed(v_as_1839_, v_i_1841_);
lean_inc(v_fst_1853_);
lean_inc(v_fst_1857_);
v___f_1884_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1884_, 0, v_fst_1857_);
lean_closure_set(v___f_1884_, 1, v_fst_1853_);
lean_closure_set(v___f_1884_, 2, v___x_1882_);
v___x_1885_ = lean_array_fget(v_array_1865_, v_start_1866_);
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_nat_add(v_start_1866_, v___x_1886_);
lean_dec(v_start_1866_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v___x_1887_);
v___x_1889_ = v___x_1880_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_array_1865_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_stop_1867_);
v___x_1889_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v_foundMVars_1891_; lean_object* v_hypothesesPos_1892_; uint8_t v___y_1907_; uint8_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = lean_unbox(v___x_1885_);
lean_dec(v___x_1885_);
v___x_1936_ = l_Lean_BinderInfo_isExplicit(v___x_1935_);
if (v___x_1936_ == 0)
{
v___y_1907_ = v___x_1936_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = l_Lean_Expr_mvarId_x21(v_a_1883_);
v___x_1938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_1937_, v_fst_1853_);
lean_dec(v___x_1937_);
if (v___x_1938_ == 0)
{
v___y_1907_ = v___x_1936_;
goto v___jp_1906_;
}
else
{
lean_dec_ref(v___f_1884_);
v_foundMVars_1891_ = v_fst_1853_;
v_hypothesesPos_1892_ = v_fst_1861_;
goto v___jp_1890_;
}
}
v___jp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_nat_add(v_fst_1857_, v___x_1886_);
lean_dec(v_fst_1857_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1889_);
lean_ctor_set(v___x_1863_, 0, v_hypothesesPos_1892_);
v___x_1895_ = v___x_1863_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_hypothesesPos_1892_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1889_);
v___x_1895_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1895_);
lean_ctor_set(v___x_1859_, 0, v___x_1893_);
v___x_1897_ = v___x_1859_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1899_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1897_);
lean_ctor_set(v___x_1855_, 0, v_foundMVars_1891_);
v___x_1899_ = v___x_1855_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_foundMVars_1891_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
size_t v___x_1900_; size_t v___x_1901_; 
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1841_, v___x_1900_);
v_i_1841_ = v___x_1901_;
v_b_1842_ = v___x_1899_;
goto _start;
}
}
}
}
v___jp_1906_:
{
if (v___y_1907_ == 0)
{
lean_dec_ref(v___f_1884_);
v_foundMVars_1891_ = v_fst_1853_;
v_hypothesesPos_1892_ = v_fst_1861_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1908_; 
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v_a_1883_);
v___x_1908_ = lean_infer_type(v_a_1883_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = 0;
v___x_1911_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_a_1909_, v___f_1884_, v___x_1910_, v___x_1910_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
if (lean_obj_tag(v_a_1912_) == 0)
{
v_foundMVars_1891_ = v_fst_1853_;
v_hypothesesPos_1892_ = v_fst_1861_;
goto v___jp_1890_;
}
else
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_val_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v_a_1912_);
v___x_1914_ = l_Lean_Expr_mvarId_x21(v_a_1883_);
v___x_1915_ = l_Lean_MVarIdSet_insert(v_fst_1853_, v___x_1914_);
v___x_1916_ = l_Lean_Expr_mvarId_x21(v_val_1913_);
lean_dec(v_val_1913_);
v___x_1917_ = l_Lean_MVarIdSet_insert(v___x_1915_, v___x_1916_);
lean_inc(v_fst_1857_);
v___x_1918_ = lean_array_push(v_fst_1861_, v_fst_1857_);
v_foundMVars_1891_ = v___x_1917_;
v_hypothesesPos_1892_ = v___x_1918_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___x_1889_);
lean_del_object(v___x_1863_);
lean_dec(v_fst_1861_);
lean_del_object(v___x_1859_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
v_a_1919_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1911_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1911_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v___x_1889_);
lean_dec_ref(v___f_1884_);
lean_del_object(v___x_1863_);
lean_dec(v_fst_1861_);
lean_del_object(v___x_1859_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
v_a_1927_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1908_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1908_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(lean_object* v_as_1950_, lean_object* v_sz_1951_, lean_object* v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1951_);
lean_dec(v_sz_1951_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_as_1950_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_as_1950_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(lean_object* v_as_1962_, size_t v_sz_1963_, size_t v_i_1964_, lean_object* v_b_1965_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_lt(v_i_1964_, v_sz_1963_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_b_1965_);
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; 
v_a_1969_ = lean_array_uget_borrowed(v_as_1962_, v_i_1964_);
lean_inc(v_a_1969_);
v___x_1970_ = l_Lean_MVarIdSet_insert(v_b_1965_, v_a_1969_);
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1964_, v___x_1971_);
v_i_1964_ = v___x_1972_;
v_b_1965_ = v___x_1970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(lean_object* v_as_1974_, lean_object* v_sz_1975_, lean_object* v_i_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_){
_start:
{
size_t v_sz_boxed_1979_; size_t v_i_boxed_1980_; lean_object* v_res_1981_; 
v_sz_boxed_1979_ = lean_unbox_usize(v_sz_1975_);
lean_dec(v_sz_1975_);
v_i_boxed_1980_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_1974_, v_sz_boxed_1979_, v_i_boxed_1980_, v_b_1977_);
lean_dec_ref(v_as_1974_);
return v_res_1981_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_unsigned_to_nat(16u);
v___x_1984_ = lean_mk_array(v___x_1983_, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0);
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___x_1985_);
return v___x_1987_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2));
v___x_1991_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___x_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(lean_object* v_as_1993_, size_t v_sz_1994_, size_t v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_b_1996_);
return v___x_2003_;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_result_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_a_2004_ = lean_array_uget_borrowed(v_as_1993_, v_i_1995_);
v___x_2005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3);
lean_inc(v_a_2004_);
v___x_2006_ = l_Lean_Expr_collectMVars(v___x_2005_, v_a_2004_);
v_result_2007_ = lean_ctor_get(v___x_2006_, 1);
lean_inc_ref(v_result_2007_);
lean_dec_ref(v___x_2006_);
v_sz_2008_ = lean_array_size(v_result_2007_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_result_2007_, v_sz_2008_, v___x_2009_, v_b_1996_);
lean_dec_ref(v_result_2007_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; size_t v___x_2012_; size_t v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_1995_, v___x_2012_);
v_i_1995_ = v___x_2013_;
v_b_1996_ = v_a_2011_;
goto _start;
}
else
{
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___boxed(lean_object* v_as_2015_, lean_object* v_sz_2016_, lean_object* v_i_2017_, lean_object* v_b_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2016_);
lean_dec(v_sz_2016_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_as_2015_, v_sz_boxed_2024_, v_i_boxed_2025_, v_b_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_as_2015_);
return v_res_2026_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(lean_object* v_lhsArgs_2032_, lean_object* v_fst_2033_, lean_object* v_fst_2034_, lean_object* v_lhsFn_2035_, lean_object* v_declName_2036_, lean_object* v_prio_2037_, lean_object* v_snd_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 5)
{
lean_object* v_fn_2047_; lean_object* v_arg_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_fn_2047_ = lean_ctor_get(v_x_2039_, 0);
lean_inc_ref(v_fn_2047_);
v_arg_2048_ = lean_ctor_get(v_x_2039_, 1);
lean_inc_ref(v_arg_2048_);
lean_dec_ref(v_x_2039_);
v___x_2049_ = lean_array_set(v_x_2040_, v_x_2041_, v_arg_2048_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_sub(v_x_2041_, v___x_2050_);
lean_dec(v_x_2041_);
v_x_2039_ = v_fn_2047_;
v_x_2040_ = v___x_2049_;
v_x_2041_ = v___x_2051_;
goto _start;
}
else
{
lean_object* v___x_2053_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; uint8_t v___y_2115_; uint8_t v___x_2122_; 
lean_dec(v_x_2041_);
v___x_2053_ = lean_box(1);
v___x_2122_ = l_Lean_Expr_isConst(v_lhsFn_2035_);
if (v___x_2122_ == 0)
{
v___y_2115_ = v___x_2122_;
goto v___jp_2114_;
}
else
{
uint8_t v___x_2123_; 
v___x_2123_ = l_Lean_Expr_isConst(v_x_2039_);
v___y_2115_ = v___x_2123_;
goto v___jp_2114_;
}
v___jp_2054_:
{
size_t v_sz_2059_; size_t v___x_2060_; lean_object* v___x_2061_; 
v_sz_2059_ = lean_array_size(v_lhsArgs_2032_);
v___x_2060_ = ((size_t)0ULL);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_lhsArgs_2032_, v_sz_2059_, v___x_2060_, v___x_2053_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; size_t v_sz_2070_; lean_object* v___x_2071_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2061_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0));
v___x_2065_ = lean_array_get_size(v_fst_2033_);
v___x_2066_ = l_Array_toSubarray___redArg(v_fst_2033_, v___x_2063_, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2063_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_a_2062_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v_sz_2070_ = lean_array_size(v_fst_2034_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_fst_2034_, v_sz_2070_, v___x_2060_, v___x_2069_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2084_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_snd_2076_; lean_object* v_snd_2077_; lean_object* v_fst_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v_snd_2076_ = lean_ctor_get(v_a_2072_, 1);
lean_inc(v_snd_2076_);
lean_dec(v_a_2072_);
v_snd_2077_ = lean_ctor_get(v_snd_2076_, 1);
lean_inc(v_snd_2077_);
lean_dec(v_snd_2076_);
v_fst_2078_ = lean_ctor_get(v_snd_2077_, 0);
lean_inc(v_fst_2078_);
lean_dec(v_snd_2077_);
v___x_2079_ = l_Lean_Expr_constName_x21(v_lhsFn_2035_);
v___x_2080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2080_, 0, v_declName_2036_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
lean_ctor_set(v___x_2080_, 2, v_fst_2078_);
lean_ctor_set(v___x_2080_, 3, v_prio_2037_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2080_);
v___x_2082_ = v___x_2074_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_prio_2037_);
lean_dec(v_declName_2036_);
v_a_2085_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2071_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2071_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_prio_2037_);
lean_dec(v_declName_2036_);
lean_dec_ref(v_fst_2033_);
v_a_2093_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2061_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2061_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
v___jp_2101_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v___x_2102_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2);
v___x_2103_ = l_Lean_indentExpr(v_snd_2038_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_2104_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
v___jp_2114_:
{
if (v___y_2115_ == 0)
{
lean_dec_ref(v_x_2040_);
lean_dec_ref(v_x_2039_);
lean_dec(v_prio_2037_);
lean_dec(v_declName_2036_);
lean_dec_ref(v_fst_2033_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = l_Lean_Expr_constName_x21(v_lhsFn_2035_);
v___x_2117_ = l_Lean_Expr_constName_x21(v_x_2039_);
lean_dec_ref(v_x_2039_);
v___x_2118_ = lean_name_eq(v___x_2116_, v___x_2117_);
lean_dec(v___x_2117_);
lean_dec(v___x_2116_);
if (v___x_2118_ == 0)
{
lean_dec_ref(v_x_2040_);
lean_dec(v_prio_2037_);
lean_dec(v_declName_2036_);
lean_dec_ref(v_fst_2033_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_array_get_size(v_lhsArgs_2032_);
v___x_2120_ = lean_array_get_size(v_x_2040_);
lean_dec_ref(v_x_2040_);
v___x_2121_ = lean_nat_dec_eq(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_dec(v_prio_2037_);
lean_dec(v_declName_2036_);
lean_dec_ref(v_fst_2033_);
goto v___jp_2101_;
}
else
{
lean_dec_ref(v_snd_2038_);
v___y_2055_ = v___y_2042_;
v___y_2056_ = v___y_2043_;
v___y_2057_ = v___y_2044_;
v___y_2058_ = v___y_2045_;
goto v___jp_2054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___boxed(lean_object* v_lhsArgs_2124_, lean_object* v_fst_2125_, lean_object* v_fst_2126_, lean_object* v_lhsFn_2127_, lean_object* v_declName_2128_, lean_object* v_prio_2129_, lean_object* v_snd_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_lhsArgs_2124_, v_fst_2125_, v_fst_2126_, v_lhsFn_2127_, v_declName_2128_, v_prio_2129_, v_snd_2130_, v_x_2131_, v_x_2132_, v_x_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec_ref(v_lhsFn_2127_);
lean_dec_ref(v_fst_2126_);
lean_dec_ref(v_lhsArgs_2124_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(lean_object* v_snd_2140_, lean_object* v_fst_2141_, lean_object* v_fst_2142_, lean_object* v_declName_2143_, lean_object* v_prio_2144_, lean_object* v_snd_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
if (lean_obj_tag(v_x_2146_) == 5)
{
lean_object* v_fn_2154_; lean_object* v_arg_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_fn_2154_ = lean_ctor_get(v_x_2146_, 0);
lean_inc_ref(v_fn_2154_);
v_arg_2155_ = lean_ctor_get(v_x_2146_, 1);
lean_inc_ref(v_arg_2155_);
lean_dec_ref(v_x_2146_);
v___x_2156_ = lean_array_set(v_x_2147_, v_x_2148_, v_arg_2155_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_sub(v_x_2148_, v___x_2157_);
lean_dec(v_x_2148_);
v_x_2146_ = v_fn_2154_;
v_x_2147_ = v___x_2156_;
v_x_2148_ = v___x_2158_;
goto _start;
}
else
{
lean_object* v_dummy_2160_; lean_object* v_nargs_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec(v_x_2148_);
v_dummy_2160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2161_ = l_Lean_Expr_getAppNumArgs(v_snd_2140_);
lean_inc(v_nargs_2161_);
v___x_2162_ = lean_mk_array(v_nargs_2161_, v_dummy_2160_);
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = lean_nat_sub(v_nargs_2161_, v___x_2163_);
lean_dec(v_nargs_2161_);
v___x_2165_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_x_2147_, v_fst_2141_, v_fst_2142_, v_x_2146_, v_declName_2143_, v_prio_2144_, v_snd_2145_, v_snd_2140_, v___x_2162_, v___x_2164_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v_x_2146_);
lean_dec_ref(v_x_2147_);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12___boxed(lean_object* v_snd_2166_, lean_object* v_fst_2167_, lean_object* v_fst_2168_, lean_object* v_declName_2169_, lean_object* v_prio_2170_, lean_object* v_snd_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_2166_, v_fst_2167_, v_fst_2168_, v_declName_2169_, v_prio_2170_, v_snd_2171_, v_x_2172_, v_x_2173_, v_x_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v_fst_2168_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(lean_object* v_fst_2181_, lean_object* v_fst_2182_, lean_object* v_declName_2183_, lean_object* v_prio_2184_, lean_object* v_snd_2185_, lean_object* v_snd_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 5)
{
lean_object* v_fn_2195_; lean_object* v_arg_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_fn_2195_ = lean_ctor_get(v_x_2187_, 0);
lean_inc_ref(v_fn_2195_);
v_arg_2196_ = lean_ctor_get(v_x_2187_, 1);
lean_inc_ref(v_arg_2196_);
lean_dec_ref(v_x_2187_);
v___x_2197_ = lean_array_set(v_x_2188_, v_x_2189_, v_arg_2196_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_sub(v_x_2189_, v___x_2198_);
v___x_2200_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_2186_, v_fst_2181_, v_fst_2182_, v_declName_2183_, v_prio_2184_, v_snd_2185_, v_fn_2195_, v___x_2197_, v___x_2199_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2200_;
}
else
{
lean_object* v_dummy_2201_; lean_object* v_nargs_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_dummy_2201_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2202_ = l_Lean_Expr_getAppNumArgs(v_snd_2186_);
lean_inc(v_nargs_2202_);
v___x_2203_ = lean_mk_array(v_nargs_2202_, v_dummy_2201_);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_sub(v_nargs_2202_, v___x_2204_);
lean_dec(v_nargs_2202_);
v___x_2206_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(v_x_2188_, v_fst_2181_, v_fst_2182_, v_x_2187_, v_declName_2183_, v_prio_2184_, v_snd_2185_, v_snd_2186_, v___x_2203_, v___x_2205_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec_ref(v_x_2187_);
lean_dec_ref(v_x_2188_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(lean_object* v_fst_2207_, lean_object* v_fst_2208_, lean_object* v_declName_2209_, lean_object* v_prio_2210_, lean_object* v_snd_2211_, lean_object* v_snd_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(v_fst_2207_, v_fst_2208_, v_declName_2209_, v_prio_2210_, v_snd_2211_, v_snd_2212_, v_x_2213_, v_x_2214_, v_x_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_x_2215_);
lean_dec_ref(v_fst_2208_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = l_List_reverse___redArg(v_a_2223_);
return v___x_2224_;
}
else
{
lean_object* v_head_2225_; lean_object* v_tail_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2235_; 
v_head_2225_ = lean_ctor_get(v_a_2222_, 0);
v_tail_2226_ = lean_ctor_get(v_a_2222_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2228_ = v_a_2222_;
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_tail_2226_);
lean_inc(v_head_2225_);
lean_dec(v_a_2222_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2230_ = l_Lean_mkLevelParam(v_head_2225_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v_a_2223_);
lean_ctor_set(v___x_2228_, 0, v___x_2230_);
v___x_2232_ = v___x_2228_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_a_2223_);
v___x_2232_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
v_a_2222_ = v_tail_2226_;
v_a_2223_ = v___x_2232_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
lean_ctor_set(v___x_2241_, 2, v___x_2240_);
lean_ctor_set(v___x_2241_, 3, v___x_2240_);
lean_ctor_set(v___x_2241_, 4, v___x_2239_);
lean_ctor_set(v___x_2241_, 5, v___x_2239_);
lean_ctor_set(v___x_2241_, 6, v___x_2239_);
lean_ctor_set(v___x_2241_, 7, v___x_2239_);
lean_ctor_set(v___x_2241_, 8, v___x_2239_);
lean_ctor_set(v___x_2241_, 9, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_unsigned_to_nat(32u);
v___x_2243_ = lean_mk_empty_array_with_capacity(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2245_ = ((size_t)5ULL);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_unsigned_to_nat(32u);
v___x_2248_ = lean_mk_empty_array_with_capacity(v___x_2247_);
v___x_2249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_2250_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
lean_ctor_set(v___x_2250_, 2, v___x_2246_);
lean_ctor_set(v___x_2250_, 3, v___x_2246_);
lean_ctor_set_usize(v___x_2250_, 4, v___x_2245_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2251_ = lean_box(1);
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_2254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2252_);
lean_ctor_set(v___x_2254_, 2, v___x_2251_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_2260_ = l_Lean_stringToMessageData(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; lean_object* v_env_2281_; uint8_t v___x_2282_; 
v___x_2280_ = lean_st_ref_get(v___y_2278_);
v_env_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_env_2281_);
lean_dec(v___x_2280_);
v___x_2282_ = l_Lean_Name_isAnonymous(v_declHint_2277_);
if (v___x_2282_ == 0)
{
uint8_t v_isExporting_2283_; 
v_isExporting_2283_ = lean_ctor_get_uint8(v_env_2281_, sizeof(void*)*8);
if (v_isExporting_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec_ref(v_env_2281_);
lean_dec(v_declHint_2277_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_msg_2276_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
lean_inc_ref(v_env_2281_);
v___x_2285_ = l_Lean_Environment_setExporting(v_env_2281_, v___x_2282_);
lean_inc(v_declHint_2277_);
lean_inc_ref(v___x_2285_);
v___x_2286_ = l_Lean_Environment_contains(v___x_2285_, v_declHint_2277_, v_isExporting_2283_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_dec_ref(v___x_2285_);
lean_dec_ref(v_env_2281_);
lean_dec(v_declHint_2277_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_msg_2276_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_c_2293_; lean_object* v___x_2294_; 
v___x_2288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_2289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_2290_ = l_Lean_Options_empty;
v___x_2291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2285_);
lean_ctor_set(v___x_2291_, 1, v___x_2288_);
lean_ctor_set(v___x_2291_, 2, v___x_2289_);
lean_ctor_set(v___x_2291_, 3, v___x_2290_);
lean_inc(v_declHint_2277_);
v___x_2292_ = l_Lean_MessageData_ofConstName(v_declHint_2277_, v___x_2282_);
v_c_2293_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2293_, 0, v___x_2291_);
lean_ctor_set(v_c_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2281_, v_declHint_2277_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_env_2281_);
lean_dec(v_declHint_2277_);
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v_c_2293_);
v___x_2297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = l_Lean_MessageData_note(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_msg_2276_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
else
{
lean_object* v_val_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2337_; 
v_val_2302_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2304_ = v___x_2294_;
v_isShared_2305_ = v_isSharedCheck_2337_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_val_2302_);
lean_dec(v___x_2294_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2337_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_mod_2309_; uint8_t v___x_2310_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Lean_Environment_header(v_env_2281_);
lean_dec_ref(v_env_2281_);
v___x_2308_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2307_);
v_mod_2309_ = lean_array_get(v___x_2306_, v___x_2308_, v_val_2302_);
lean_dec(v_val_2302_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l_Lean_isPrivateName(v_declHint_2277_);
lean_dec(v_declHint_2277_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v_c_2293_);
v___x_2313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = l_Lean_MessageData_ofName(v_mod_2309_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_note(v___x_2318_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v_msg_2276_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2320_);
v___x_2322_ = v___x_2304_;
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
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v_c_2293_);
v___x_2326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_MessageData_ofName(v_mod_2309_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_MessageData_note(v___x_2331_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_msg_2276_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2333_);
v___x_2335_ = v___x_2304_;
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
}
}
else
{
lean_object* v___x_2338_; 
lean_dec_ref(v_env_2281_);
lean_dec(v_declHint_2277_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_msg_2276_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_2339_, lean_object* v_declHint_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2339_, v_declHint_2340_, v___y_2341_);
lean_dec(v___y_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(lean_object* v_msg_2344_, lean_object* v_declHint_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2361_; 
v___x_2351_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2344_, v_declHint_2345_, v___y_2349_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = l_Lean_unknownIdentifierMessageTag;
v___x_2357_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v_a_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16___boxed(lean_object* v_msg_2362_, lean_object* v_declHint_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_2362_, v_declHint_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(lean_object* v_ref_2370_, lean_object* v_msg_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_fileName_2377_; lean_object* v_fileMap_2378_; lean_object* v_options_2379_; lean_object* v_currRecDepth_2380_; lean_object* v_maxRecDepth_2381_; lean_object* v_ref_2382_; lean_object* v_currNamespace_2383_; lean_object* v_openDecls_2384_; lean_object* v_initHeartbeats_2385_; lean_object* v_maxHeartbeats_2386_; lean_object* v_quotContext_2387_; lean_object* v_currMacroScope_2388_; uint8_t v_diag_2389_; lean_object* v_cancelTk_x3f_2390_; uint8_t v_suppressElabErrors_2391_; lean_object* v_inheritedTraceOptions_2392_; lean_object* v_ref_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_fileName_2377_ = lean_ctor_get(v___y_2374_, 0);
v_fileMap_2378_ = lean_ctor_get(v___y_2374_, 1);
v_options_2379_ = lean_ctor_get(v___y_2374_, 2);
v_currRecDepth_2380_ = lean_ctor_get(v___y_2374_, 3);
v_maxRecDepth_2381_ = lean_ctor_get(v___y_2374_, 4);
v_ref_2382_ = lean_ctor_get(v___y_2374_, 5);
v_currNamespace_2383_ = lean_ctor_get(v___y_2374_, 6);
v_openDecls_2384_ = lean_ctor_get(v___y_2374_, 7);
v_initHeartbeats_2385_ = lean_ctor_get(v___y_2374_, 8);
v_maxHeartbeats_2386_ = lean_ctor_get(v___y_2374_, 9);
v_quotContext_2387_ = lean_ctor_get(v___y_2374_, 10);
v_currMacroScope_2388_ = lean_ctor_get(v___y_2374_, 11);
v_diag_2389_ = lean_ctor_get_uint8(v___y_2374_, sizeof(void*)*14);
v_cancelTk_x3f_2390_ = lean_ctor_get(v___y_2374_, 12);
v_suppressElabErrors_2391_ = lean_ctor_get_uint8(v___y_2374_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2392_ = lean_ctor_get(v___y_2374_, 13);
v_ref_2393_ = l_Lean_replaceRef(v_ref_2370_, v_ref_2382_);
lean_inc_ref(v_inheritedTraceOptions_2392_);
lean_inc(v_cancelTk_x3f_2390_);
lean_inc(v_currMacroScope_2388_);
lean_inc(v_quotContext_2387_);
lean_inc(v_maxHeartbeats_2386_);
lean_inc(v_initHeartbeats_2385_);
lean_inc(v_openDecls_2384_);
lean_inc(v_currNamespace_2383_);
lean_inc(v_maxRecDepth_2381_);
lean_inc(v_currRecDepth_2380_);
lean_inc_ref(v_options_2379_);
lean_inc_ref(v_fileMap_2378_);
lean_inc_ref(v_fileName_2377_);
v___x_2394_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2394_, 0, v_fileName_2377_);
lean_ctor_set(v___x_2394_, 1, v_fileMap_2378_);
lean_ctor_set(v___x_2394_, 2, v_options_2379_);
lean_ctor_set(v___x_2394_, 3, v_currRecDepth_2380_);
lean_ctor_set(v___x_2394_, 4, v_maxRecDepth_2381_);
lean_ctor_set(v___x_2394_, 5, v_ref_2393_);
lean_ctor_set(v___x_2394_, 6, v_currNamespace_2383_);
lean_ctor_set(v___x_2394_, 7, v_openDecls_2384_);
lean_ctor_set(v___x_2394_, 8, v_initHeartbeats_2385_);
lean_ctor_set(v___x_2394_, 9, v_maxHeartbeats_2386_);
lean_ctor_set(v___x_2394_, 10, v_quotContext_2387_);
lean_ctor_set(v___x_2394_, 11, v_currMacroScope_2388_);
lean_ctor_set(v___x_2394_, 12, v_cancelTk_x3f_2390_);
lean_ctor_set(v___x_2394_, 13, v_inheritedTraceOptions_2392_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*14, v_diag_2389_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*14 + 1, v_suppressElabErrors_2391_);
v___x_2395_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_2371_, v___y_2372_, v___y_2373_, v___x_2394_, v___y_2375_);
lean_dec_ref(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2396_, v_msg_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(lean_object* v_ref_2404_, lean_object* v_msg_2405_, lean_object* v_declHint_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_2405_, v_declHint_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2404_, v_a_2413_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg___boxed(lean_object* v_ref_2415_, lean_object* v_msg_2416_, lean_object* v_declHint_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2415_, v_msg_2416_, v_declHint_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_ref_2415_);
return v_res_2423_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(lean_object* v_ref_2430_, lean_object* v_constName_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2437_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1);
v___x_2438_ = 0;
lean_inc(v_constName_2431_);
v___x_2439_ = l_Lean_MessageData_ofConstName(v_constName_2431_, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2437_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2430_, v___x_2442_, v_constName_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_ref_2444_, lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2444_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v_ref_2444_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(lean_object* v_constName_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_ref_2458_; lean_object* v___x_2459_; 
v_ref_2458_ = lean_ctor_get(v___y_2455_, 5);
v___x_2459_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2458_, v_constName_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_constName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object* v_constName_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v_env_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_st_ref_get(v___y_2471_);
v_env_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_env_2474_);
lean_dec(v___x_2473_);
v___x_2475_ = 0;
lean_inc(v_constName_2467_);
v___x_2476_ = l_Lean_Environment_findConstVal_x3f(v_env_2474_, v_constName_2467_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2477_;
}
else
{
lean_object* v_val_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_constName_2467_);
v_val_2478_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_val_2478_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 0);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_val_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(lean_object* v_constName_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object* v_constName_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
lean_inc(v_constName_2493_);
v___x_2499_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2511_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2511_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2511_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_levelParams_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v_levelParams_2504_ = lean_ctor_get(v_a_2500_, 1);
lean_inc(v_levelParams_2504_);
lean_dec(v_a_2500_);
v___x_2505_ = lean_box(0);
v___x_2506_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(v_levelParams_2504_, v___x_2505_);
v___x_2507_ = l_Lean_mkConst(v_constName_2493_, v___x_2506_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2507_);
v___x_2509_ = v___x_2502_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_constName_2493_);
v_a_2512_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2499_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2499_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(lean_object* v_constName_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(v_constName_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2526_;
}
}
static uint64_t _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0(void){
_start:
{
uint8_t v___x_2527_; uint64_t v___x_2528_; 
v___x_2527_ = 2;
v___x_2528_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_Meta_mkSimpCongrTheorem___closed__1));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem(lean_object* v_declName_2532_, lean_object* v_prio_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; uint8_t v_foApprox_2540_; uint8_t v_ctxApprox_2541_; uint8_t v_quasiPatternApprox_2542_; uint8_t v_constApprox_2543_; uint8_t v_isDefEqStuckEx_2544_; uint8_t v_unificationHints_2545_; uint8_t v_proofIrrelevance_2546_; uint8_t v_assignSyntheticOpaque_2547_; uint8_t v_offsetCnstrs_2548_; uint8_t v_etaStruct_2549_; uint8_t v_univApprox_2550_; uint8_t v_iota_2551_; uint8_t v_beta_2552_; uint8_t v_proj_2553_; uint8_t v_zeta_2554_; uint8_t v_zetaDelta_2555_; uint8_t v_zetaUnused_2556_; uint8_t v_zetaHave_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2650_; 
v___x_2539_ = l_Lean_Meta_Context_config(v_a_2534_);
v_foApprox_2540_ = lean_ctor_get_uint8(v___x_2539_, 0);
v_ctxApprox_2541_ = lean_ctor_get_uint8(v___x_2539_, 1);
v_quasiPatternApprox_2542_ = lean_ctor_get_uint8(v___x_2539_, 2);
v_constApprox_2543_ = lean_ctor_get_uint8(v___x_2539_, 3);
v_isDefEqStuckEx_2544_ = lean_ctor_get_uint8(v___x_2539_, 4);
v_unificationHints_2545_ = lean_ctor_get_uint8(v___x_2539_, 5);
v_proofIrrelevance_2546_ = lean_ctor_get_uint8(v___x_2539_, 6);
v_assignSyntheticOpaque_2547_ = lean_ctor_get_uint8(v___x_2539_, 7);
v_offsetCnstrs_2548_ = lean_ctor_get_uint8(v___x_2539_, 8);
v_etaStruct_2549_ = lean_ctor_get_uint8(v___x_2539_, 10);
v_univApprox_2550_ = lean_ctor_get_uint8(v___x_2539_, 11);
v_iota_2551_ = lean_ctor_get_uint8(v___x_2539_, 12);
v_beta_2552_ = lean_ctor_get_uint8(v___x_2539_, 13);
v_proj_2553_ = lean_ctor_get_uint8(v___x_2539_, 14);
v_zeta_2554_ = lean_ctor_get_uint8(v___x_2539_, 15);
v_zetaDelta_2555_ = lean_ctor_get_uint8(v___x_2539_, 16);
v_zetaUnused_2556_ = lean_ctor_get_uint8(v___x_2539_, 17);
v_zetaHave_2557_ = lean_ctor_get_uint8(v___x_2539_, 18);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2559_ = v___x_2539_;
v_isShared_2560_ = v_isSharedCheck_2650_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2539_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2650_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
uint8_t v_trackZetaDelta_2561_; lean_object* v_zetaDeltaSet_2562_; lean_object* v_lctx_2563_; lean_object* v_localInstances_2564_; lean_object* v_defEqCtx_x3f_2565_; lean_object* v_synthPendingDepth_2566_; lean_object* v_canUnfold_x3f_2567_; uint8_t v_univApprox_2568_; uint8_t v_inTypeClassResolution_2569_; uint8_t v_cacheInferType_2570_; uint8_t v___x_2571_; lean_object* v_config_2573_; 
v_trackZetaDelta_2561_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*7);
v_zetaDeltaSet_2562_ = lean_ctor_get(v_a_2534_, 1);
v_lctx_2563_ = lean_ctor_get(v_a_2534_, 2);
v_localInstances_2564_ = lean_ctor_get(v_a_2534_, 3);
v_defEqCtx_x3f_2565_ = lean_ctor_get(v_a_2534_, 4);
v_synthPendingDepth_2566_ = lean_ctor_get(v_a_2534_, 5);
v_canUnfold_x3f_2567_ = lean_ctor_get(v_a_2534_, 6);
v_univApprox_2568_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2569_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*7 + 2);
v_cacheInferType_2570_ = lean_ctor_get_uint8(v_a_2534_, sizeof(void*)*7 + 3);
v___x_2571_ = 2;
if (v_isShared_2560_ == 0)
{
v_config_2573_ = v___x_2559_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 0, v_foApprox_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 1, v_ctxApprox_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 2, v_quasiPatternApprox_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 3, v_constApprox_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 4, v_isDefEqStuckEx_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 5, v_unificationHints_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 6, v_proofIrrelevance_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 7, v_assignSyntheticOpaque_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 8, v_offsetCnstrs_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 10, v_etaStruct_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 11, v_univApprox_2550_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 12, v_iota_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 13, v_beta_2552_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 14, v_proj_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 15, v_zeta_2554_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 16, v_zetaDelta_2555_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 17, v_zetaUnused_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, 18, v_zetaHave_2557_);
v_config_2573_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
uint64_t v___x_2574_; uint64_t v___x_2575_; uint64_t v___x_2576_; uint64_t v___x_2577_; uint64_t v___x_2578_; uint64_t v_key_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_ctor_set_uint8(v_config_2573_, 9, v___x_2571_);
v___x_2574_ = l_Lean_Meta_Context_configKey(v_a_2534_);
v___x_2575_ = 2ULL;
v___x_2576_ = lean_uint64_shift_right(v___x_2574_, v___x_2575_);
v___x_2577_ = lean_uint64_shift_left(v___x_2576_, v___x_2575_);
v___x_2578_ = lean_uint64_once(&l_Lean_Meta_mkSimpCongrTheorem___closed__0, &l_Lean_Meta_mkSimpCongrTheorem___closed__0_once, _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0);
v_key_2579_ = lean_uint64_lor(v___x_2577_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2580_, 0, v_config_2573_);
lean_ctor_set_uint64(v___x_2580_, sizeof(void*)*1, v_key_2579_);
lean_inc(v_canUnfold_x3f_2567_);
lean_inc(v_synthPendingDepth_2566_);
lean_inc(v_defEqCtx_x3f_2565_);
lean_inc_ref(v_localInstances_2564_);
lean_inc_ref(v_lctx_2563_);
lean_inc(v_zetaDeltaSet_2562_);
v___x_2581_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v_zetaDeltaSet_2562_);
lean_ctor_set(v___x_2581_, 2, v_lctx_2563_);
lean_ctor_set(v___x_2581_, 3, v_localInstances_2564_);
lean_ctor_set(v___x_2581_, 4, v_defEqCtx_x3f_2565_);
lean_ctor_set(v___x_2581_, 5, v_synthPendingDepth_2566_);
lean_ctor_set(v___x_2581_, 6, v_canUnfold_x3f_2567_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*7, v_trackZetaDelta_2561_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*7 + 1, v_univApprox_2568_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2569_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*7 + 3, v_cacheInferType_2570_);
lean_inc(v_declName_2532_);
v___x_2582_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(v_declName_2532_, v___x_2581_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
lean_inc(v_a_2537_);
lean_inc_ref(v_a_2536_);
lean_inc(v_a_2535_);
lean_inc_ref(v___x_2581_);
v___x_2584_ = lean_infer_type(v_a_2583_, v___x_2581_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = lean_box(0);
v___x_2587_ = 0;
v___x_2588_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2585_, v___x_2586_, v___x_2587_, v___x_2581_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v_snd_2590_; lean_object* v_fst_2591_; lean_object* v_fst_2592_; lean_object* v_snd_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2624_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v_snd_2590_ = lean_ctor_get(v_a_2589_, 1);
lean_inc(v_snd_2590_);
v_fst_2591_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_fst_2591_);
lean_dec(v_a_2589_);
v_fst_2592_ = lean_ctor_get(v_snd_2590_, 0);
v_snd_2593_ = lean_ctor_get(v_snd_2590_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_snd_2590_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2595_ = v_snd_2590_;
v_isShared_2596_ = v_isSharedCheck_2624_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snd_2593_);
lean_inc(v_fst_2592_);
lean_dec(v_snd_2590_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2624_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2598_; lean_object* v_snd_2599_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8));
v___x_2607_ = lean_unsigned_to_nat(3u);
v___x_2608_ = l_Lean_Expr_isAppOfArity(v_snd_2593_, v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10));
v___x_2610_ = lean_unsigned_to_nat(2u);
v___x_2611_ = l_Lean_Expr_isAppOfArity(v_snd_2593_, v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_dec(v_fst_2592_);
lean_dec(v_fst_2591_);
lean_dec(v_prio_2533_);
lean_dec(v_declName_2532_);
v___x_2612_ = lean_obj_once(&l_Lean_Meta_mkSimpCongrTheorem___closed__2, &l_Lean_Meta_mkSimpCongrTheorem___closed__2_once, _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2);
v___x_2613_ = l_Lean_indentExpr(v_snd_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 7);
lean_ctor_set(v___x_2595_, 1, v___x_2613_);
lean_ctor_set(v___x_2595_, 0, v___x_2612_);
v___x_2615_ = v___x_2595_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_2615_, v___x_2581_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec_ref(v___x_2581_);
return v___x_2616_;
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_del_object(v___x_2595_);
v___x_2618_ = l_Lean_Expr_appFn_x21(v_snd_2593_);
v___x_2619_ = l_Lean_Expr_appArg_x21(v___x_2618_);
lean_dec_ref(v___x_2618_);
v___x_2620_ = l_Lean_Expr_appArg_x21(v_snd_2593_);
v_fst_2598_ = v___x_2619_;
v_snd_2599_ = v___x_2620_;
goto v___jp_2597_;
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_del_object(v___x_2595_);
v___x_2621_ = l_Lean_Expr_appFn_x21(v_snd_2593_);
v___x_2622_ = l_Lean_Expr_appArg_x21(v___x_2621_);
lean_dec_ref(v___x_2621_);
v___x_2623_ = l_Lean_Expr_appArg_x21(v_snd_2593_);
v_fst_2598_ = v___x_2622_;
v_snd_2599_ = v___x_2623_;
goto v___jp_2597_;
}
v___jp_2597_:
{
lean_object* v_dummy_2600_; lean_object* v_nargs_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_dummy_2600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
v_nargs_2601_ = l_Lean_Expr_getAppNumArgs(v_fst_2598_);
lean_inc(v_nargs_2601_);
v___x_2602_ = lean_mk_array(v_nargs_2601_, v_dummy_2600_);
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_sub(v_nargs_2601_, v___x_2603_);
lean_dec(v_nargs_2601_);
v___x_2605_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(v_fst_2592_, v_fst_2591_, v_declName_2532_, v_prio_2533_, v_snd_2593_, v_snd_2599_, v_fst_2598_, v___x_2602_, v___x_2604_, v___x_2581_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec_ref(v___x_2581_);
lean_dec(v___x_2604_);
lean_dec(v_fst_2591_);
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___x_2581_);
lean_dec(v_prio_2533_);
lean_dec(v_declName_2532_);
v_a_2625_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2588_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2588_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v___x_2581_);
lean_dec(v_prio_2533_);
lean_dec(v_declName_2532_);
v_a_2633_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2584_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2584_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v___x_2581_);
lean_dec(v_prio_2533_);
lean_dec(v_declName_2532_);
v_a_2641_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2582_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2582_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpCongrTheorem___boxed(lean_object* v_declName_2651_, lean_object* v_prio_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_Meta_mkSimpCongrTheorem(v_declName_2651_, v_prio_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(lean_object* v_as_2659_, size_t v_sz_2660_, size_t v_i_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_2659_, v_sz_2660_, v_i_2661_, v_b_2662_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(lean_object* v_as_2669_, lean_object* v_sz_2670_, lean_object* v_i_2671_, lean_object* v_b_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
size_t v_sz_boxed_2678_; size_t v_i_boxed_2679_; lean_object* v_res_2680_; 
v_sz_boxed_2678_ = lean_unbox_usize(v_sz_2670_);
lean_dec(v_sz_2670_);
v_i_boxed_2679_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(v_as_2669_, v_sz_boxed_2678_, v_i_boxed_2679_, v_b_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_as_2669_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(lean_object* v_00_u03b1_2681_, lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v_msg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___boxed(lean_object* v_00_u03b1_2689_, lean_object* v_msg_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(v_00_u03b1_2689_, v_msg_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(lean_object* v_00_u03b1_2697_, lean_object* v_constName_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_constName_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(v_00_u03b1_2705_, v_constName_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(lean_object* v_00_u03b1_2713_, lean_object* v_ref_2714_, lean_object* v_constName_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_2714_, v_constName_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_ref_2723_, lean_object* v_constName_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(v_00_u03b1_2722_, v_ref_2723_, v_constName_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v_ref_2723_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(lean_object* v_00_u03b1_2731_, lean_object* v_ref_2732_, lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_2732_, v_msg_2733_, v_declHint_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_ref_2742_, lean_object* v_msg_2743_, lean_object* v_declHint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(v_00_u03b1_2741_, v_ref_2742_, v_msg_2743_, v_declHint_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v_ref_2742_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(lean_object* v_msg_2751_, lean_object* v_declHint_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_2751_, v_declHint_2752_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2759_, lean_object* v_declHint_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(v_msg_2759_, v_declHint_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(lean_object* v_00_u03b1_2767_, lean_object* v_ref_2768_, lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_2768_, v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_ref_2777_, lean_object* v_msg_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(v_00_u03b1_2776_, v_ref_2777_, v_msg_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_ref_2777_);
return v_res_2784_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
v___x_2791_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_ctor_set(v___x_2791_, 2, v___x_2790_);
lean_ctor_set(v___x_2791_, 3, v___x_2790_);
lean_ctor_set(v___x_2791_, 4, v___x_2790_);
lean_ctor_set(v___x_2791_, 5, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(lean_object* v_ext_2792_, lean_object* v_b_2793_, uint8_t v_kind_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_currNamespace_2799_; lean_object* v___x_2800_; lean_object* v_env_2801_; lean_object* v_nextMacroScope_2802_; lean_object* v_ngen_2803_; lean_object* v_auxDeclNGen_2804_; lean_object* v_traceState_2805_; lean_object* v_messages_2806_; lean_object* v_infoState_2807_; lean_object* v_snapshotTasks_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2835_; 
v_currNamespace_2799_ = lean_ctor_get(v___y_2796_, 6);
v___x_2800_ = lean_st_ref_take(v___y_2797_);
v_env_2801_ = lean_ctor_get(v___x_2800_, 0);
v_nextMacroScope_2802_ = lean_ctor_get(v___x_2800_, 1);
v_ngen_2803_ = lean_ctor_get(v___x_2800_, 2);
v_auxDeclNGen_2804_ = lean_ctor_get(v___x_2800_, 3);
v_traceState_2805_ = lean_ctor_get(v___x_2800_, 4);
v_messages_2806_ = lean_ctor_get(v___x_2800_, 6);
v_infoState_2807_ = lean_ctor_get(v___x_2800_, 7);
v_snapshotTasks_2808_ = lean_ctor_get(v___x_2800_, 8);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2800_, 5);
lean_dec(v_unused_2836_);
v___x_2810_ = v___x_2800_;
v_isShared_2811_ = v_isSharedCheck_2835_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_snapshotTasks_2808_);
lean_inc(v_infoState_2807_);
lean_inc(v_messages_2806_);
lean_inc(v_traceState_2805_);
lean_inc(v_auxDeclNGen_2804_);
lean_inc(v_ngen_2803_);
lean_inc(v_nextMacroScope_2802_);
lean_inc(v_env_2801_);
lean_dec(v___x_2800_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2835_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_inc(v_currNamespace_2799_);
v___x_2812_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2801_, v_ext_2792_, v_b_2793_, v_kind_2794_, v_currNamespace_2799_);
v___x_2813_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 5, v___x_2813_);
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_nextMacroScope_2802_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v_ngen_2803_);
lean_ctor_set(v_reuseFailAlloc_2834_, 3, v_auxDeclNGen_2804_);
lean_ctor_set(v_reuseFailAlloc_2834_, 4, v_traceState_2805_);
lean_ctor_set(v_reuseFailAlloc_2834_, 5, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2834_, 6, v_messages_2806_);
lean_ctor_set(v_reuseFailAlloc_2834_, 7, v_infoState_2807_);
lean_ctor_set(v_reuseFailAlloc_2834_, 8, v_snapshotTasks_2808_);
v___x_2815_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v_mctx_2818_; lean_object* v_zetaDeltaFVarIds_2819_; lean_object* v_postponed_2820_; lean_object* v_diag_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2832_; 
v___x_2816_ = lean_st_ref_set(v___y_2797_, v___x_2815_);
v___x_2817_ = lean_st_ref_take(v___y_2795_);
v_mctx_2818_ = lean_ctor_get(v___x_2817_, 0);
v_zetaDeltaFVarIds_2819_ = lean_ctor_get(v___x_2817_, 2);
v_postponed_2820_ = lean_ctor_get(v___x_2817_, 3);
v_diag_2821_ = lean_ctor_get(v___x_2817_, 4);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2817_, 1);
lean_dec(v_unused_2833_);
v___x_2823_ = v___x_2817_;
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_diag_2821_);
lean_inc(v_postponed_2820_);
lean_inc(v_zetaDeltaFVarIds_2819_);
lean_inc(v_mctx_2818_);
lean_dec(v___x_2817_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_mctx_2818_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_zetaDeltaFVarIds_2819_);
lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_postponed_2820_);
lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_diag_2821_);
v___x_2827_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_st_ref_set(v___y_2795_, v___x_2827_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(lean_object* v_ext_2837_, lean_object* v_b_2838_, lean_object* v_kind_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
uint8_t v_kind_boxed_2844_; lean_object* v_res_2845_; 
v_kind_boxed_2844_ = lean_unbox(v_kind_2839_);
v_res_2845_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v_ext_2837_, v_b_2838_, v_kind_boxed_2844_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(lean_object* v_00_u03b1_2846_, lean_object* v_00_u03b2_2847_, lean_object* v_00_u03c3_2848_, lean_object* v_ext_2849_, lean_object* v_b_2850_, uint8_t v_kind_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v_ext_2849_, v_b_2850_, v_kind_2851_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_00_u03b2_2859_, lean_object* v_00_u03c3_2860_, lean_object* v_ext_2861_, lean_object* v_b_2862_, lean_object* v_kind_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
uint8_t v_kind_boxed_2869_; lean_object* v_res_2870_; 
v_kind_boxed_2869_ = lean_unbox(v_kind_2863_);
v_res_2870_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(v_00_u03b1_2858_, v_00_u03b2_2859_, v_00_u03c3_2860_, v_ext_2861_, v_b_2862_, v_kind_boxed_2869_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem(lean_object* v_declName_2871_, uint8_t v_attrKind_2872_, lean_object* v_prio_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Meta_mkSimpCongrTheorem(v_declName_2871_, v_prio_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l_Lean_Meta_congrExtension;
v___x_2882_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v___x_2881_, v_a_2880_, v_attrKind_2872_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2882_;
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2879_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2879_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpCongrTheorem___boxed(lean_object* v_declName_2891_, lean_object* v_attrKind_2892_, lean_object* v_prio_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
uint8_t v_attrKind_boxed_2899_; lean_object* v_res_2900_; 
v_attrKind_boxed_2899_ = lean_unbox(v_attrKind_2892_);
v_res_2900_ = l_Lean_Meta_addSimpCongrTheorem(v_declName_2891_, v_attrKind_boxed_2899_, v_prio_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2900_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2907_; uint64_t v___x_2908_; 
v___x_2907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_2908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2907_);
return v___x_2908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_2911_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set_uint64(v___x_2911_, sizeof(void*)*1, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2916_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
lean_ctor_set(v___x_2916_, 2, v___x_2915_);
lean_ctor_set(v___x_2916_, 3, v___x_2915_);
lean_ctor_set(v___x_2916_, 4, v___x_2915_);
lean_ctor_set(v___x_2916_, 5, v___x_2915_);
return v___x_2916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
lean_ctor_set(v___x_2918_, 2, v___x_2917_);
lean_ctor_set(v___x_2918_, 3, v___x_2917_);
lean_ctor_set(v___x_2918_, 4, v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object* v___x_2919_, lean_object* v___x_2920_, lean_object* v_declName_2921_, lean_object* v_stx_2922_, uint8_t v_attrKind_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = l_Lean_Syntax_getArg(v_stx_2922_, v___x_2927_);
v___x_2929_ = l_Lean_getAttrParamOptPrio(v___x_2928_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; size_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = 0;
v___x_2932_ = 1;
v___x_2933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2935_ = lean_unsigned_to_nat(32u);
v___x_2936_ = lean_mk_empty_array_with_capacity(v___x_2935_);
v___x_2937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_2938_ = ((size_t)5ULL);
lean_inc_n(v___x_2919_, 6);
v___x_2939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2936_);
lean_ctor_set(v___x_2939_, 2, v___x_2919_);
lean_ctor_set(v___x_2939_, 3, v___x_2919_);
lean_ctor_set_usize(v___x_2939_, 4, v___x_2938_);
v___x_2940_ = lean_box(1);
lean_inc_ref(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2934_);
lean_ctor_set(v___x_2941_, 1, v___x_2939_);
lean_ctor_set(v___x_2941_, 2, v___x_2940_);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2919_);
v___x_2943_ = lean_box(0);
lean_inc(v___x_2920_);
v___x_2944_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2944_, 0, v___x_2933_);
lean_ctor_set(v___x_2944_, 1, v___x_2920_);
lean_ctor_set(v___x_2944_, 2, v___x_2941_);
lean_ctor_set(v___x_2944_, 3, v___x_2942_);
lean_ctor_set(v___x_2944_, 4, v___x_2943_);
lean_ctor_set(v___x_2944_, 5, v___x_2919_);
lean_ctor_set(v___x_2944_, 6, v___x_2943_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*7, v___x_2931_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*7 + 1, v___x_2931_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*7 + 2, v___x_2931_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*7 + 3, v___x_2932_);
v___x_2945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2919_);
lean_ctor_set(v___x_2945_, 1, v___x_2919_);
lean_ctor_set(v___x_2945_, 2, v___x_2919_);
lean_ctor_set(v___x_2945_, 3, v___x_2919_);
lean_ctor_set(v___x_2945_, 4, v___x_2934_);
lean_ctor_set(v___x_2945_, 5, v___x_2934_);
lean_ctor_set(v___x_2945_, 6, v___x_2934_);
lean_ctor_set(v___x_2945_, 7, v___x_2934_);
lean_ctor_set(v___x_2945_, 8, v___x_2934_);
lean_ctor_set(v___x_2945_, 9, v___x_2934_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2947_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_2948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2945_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
lean_ctor_set(v___x_2948_, 2, v___x_2920_);
lean_ctor_set(v___x_2948_, 3, v___x_2939_);
lean_ctor_set(v___x_2948_, 4, v___x_2947_);
v___x_2949_ = lean_st_mk_ref(v___x_2948_);
v___x_2950_ = l_Lean_Meta_addSimpCongrTheorem(v_declName_2921_, v_attrKind_2923_, v_a_2930_, v___x_2944_, v___x_2949_, v___y_2924_, v___y_2925_);
lean_dec_ref(v___x_2944_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2959_; 
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v___x_2950_, 0);
lean_dec(v_unused_2960_);
v___x_2952_ = v___x_2950_;
v_isShared_2953_ = v_isSharedCheck_2959_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v___x_2950_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2959_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2954_ = lean_st_ref_get(v___x_2949_);
lean_dec(v___x_2949_);
lean_dec(v___x_2954_);
v___x_2955_ = lean_box(0);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2955_);
v___x_2957_ = v___x_2952_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_dec(v___x_2949_);
return v___x_2950_;
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_declName_2921_);
lean_dec(v___x_2920_);
lean_dec(v___x_2919_);
v_a_2961_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2929_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2929_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v_declName_2971_, lean_object* v_stx_2972_, lean_object* v_attrKind_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v_attrKind_boxed_2977_; lean_object* v_res_2978_; 
v_attrKind_boxed_2977_ = lean_unbox(v_attrKind_2973_);
v_res_2978_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_2969_, v___x_2970_, v_declName_2971_, v_stx_2972_, v_attrKind_boxed_2977_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v_stx_2972_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v_options_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2983_ = lean_st_ref_get(v___y_2981_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_env_2984_);
lean_dec(v___x_2983_);
v_options_2985_ = lean_ctor_get(v___y_2980_, 2);
v___x_2986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_2987_ = lean_unsigned_to_nat(32u);
v___x_2988_ = lean_mk_empty_array_with_capacity(v___x_2987_);
lean_dec_ref(v___x_2988_);
v___x_2989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
lean_inc_ref(v_options_2985_);
v___x_2990_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2990_, 0, v_env_2984_);
lean_ctor_set(v___x_2990_, 1, v___x_2986_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
lean_ctor_set(v___x_2990_, 3, v_options_2985_);
v___x_2991_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v_msgData_2979_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_ref_3002_; lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3012_; 
v_ref_3002_ = lean_ctor_get(v___y_2999_, 5);
v___x_3003_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msg_2998_, v___y_2999_, v___y_3000_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3006_ = v___x_3003_;
v_isShared_3007_ = v_isSharedCheck_3012_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3012_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
lean_inc(v_ref_3002_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_ref_3002_);
lean_ctor_set(v___x_3008_, 1, v_a_3004_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
lean_ctor_set(v___x_3006_, 0, v___x_3008_);
v___x_3010_ = v___x_3006_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(lean_object* v___x_3024_, lean_object* v_decl_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3030_ = l_Lean_MessageData_ofName(v___x_3024_);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v___x_3033_, v___y_3026_, v___y_3027_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v___x_3035_, lean_object* v_decl_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_3035_, v_decl_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v_decl_3036_);
return v_res_3040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = lean_unsigned_to_nat(3428004144u);
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3100_ = l_Lean_Name_num___override(v___x_3099_, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3104_ = l_Lean_Name_str___override(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3108_ = l_Lean_Name_str___override(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_unsigned_to_nat(2u);
v___x_3110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3111_ = l_Lean_Name_num___override(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3118_ = 0;
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3120_);
lean_ctor_set(v___x_3122_, 2, v___x_3119_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*3, v___x_3118_);
return v___x_3122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___f_3123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___f_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___f_3124_);
lean_ctor_set(v___x_3126_, 2, v___f_3123_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3129_ = l_Lean_registerBuiltinAttribute(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3132_, lean_object* v_msg_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_3133_, v___y_3134_, v___y_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_msg_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(v_00_u03b1_3138_, v_msg_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_));
v___x_3148_ = l_Lean_addBuiltinDocString(v___x_3146_, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_env_3154_; lean_object* v___x_3155_; lean_object* v_ext_3156_; lean_object* v_toEnvExtension_3157_; lean_object* v_asyncMode_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3153_ = lean_st_ref_get(v_a_3151_);
v_env_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_env_3154_);
lean_dec(v___x_3153_);
v___x_3155_ = l_Lean_Meta_congrExtension;
v_ext_3156_ = lean_ctor_get(v___x_3155_, 1);
v_toEnvExtension_3157_ = lean_ctor_get(v_ext_3156_, 0);
v_asyncMode_3158_ = lean_ctor_get(v_toEnvExtension_3157_, 2);
v___x_3159_ = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
v___x_3160_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3159_, v___x_3155_, v_env_3154_, v_asyncMode_3158_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3162_);
lean_dec(v_a_3162_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpCongrTheorems___boxed(lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Meta_getSimpCongrTheorems(v_a_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
return v_res_3172_;
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
